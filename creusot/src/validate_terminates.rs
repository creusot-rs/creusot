//! Detection of loops and mutually recursive functions.
//!
//! Care is taken around the interaction with traits, like the following example:
//! ```
//! # use creusot_contracts::*;
//! pub trait Foo {
//!     #[terminates]
//!     fn foo() {}
//! }
//!
//! impl Foo for i32 {
//!     #[terminates]
//!     fn foo() {
//!         bar::<i32>(); // infinite recursion !
//!     }
//! }
//!
//! #[terminates]
//! pub fn bar<T: Foo>() {
//!     T::foo();
//! }
//! ```
//!
//! The main idea is that `#[terminates]` functions must be ordonnable: if there exists
//! an order, such that no function can refer to a function defined before, then there
//! can be no cycles.

use crate::{
    backend::is_trusted_function,
    contracts_items,
    ctx::TranslationCtx,
    pearlite::{TermKind, TermVisitor},
    specification::contract_of,
    traits::TraitResolved,
};
use indexmap::{IndexMap, IndexSet};
use petgraph::{graph, visit::EdgeRef as _};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::{
    thir,
    ty::{
        EarlyBinder, FnDef, GenericArgKind, GenericArgs, GenericArgsRef, ParamEnv, TyCtxt, TyKind,
    },
};
use rustc_span::Span;

/// Validate that a `#[terminates]` function cannot loop indefinitely. This includes:
/// - forbidding program function from using loops of any kind (this should be relaxed
/// later).
/// - forbidding (mutual) recursive calls, especially when traits are involved.
///
/// Note that for logical functions, these are relaxed: we don't check loops, nor simple
/// recursion, because why3 will handle it for us.
pub(crate) fn validate_terminates(ctx: &mut TranslationCtx) {
    ctx.tcx.dcx().abort_if_errors(); // There may have been errors before, if a `#[terminates]` calls a non-`#[terminates]`.

    let CallGraph { graph: mut call_graph, additional_data } = CallGraph::build(ctx);

    // Detect simple recursion, and loops
    for fun_index in call_graph.node_indices() {
        let def_id = call_graph.node_weight(fun_index).unwrap().def_id();
        let function_data = &additional_data[&fun_index];
        if let Some(self_edge) = call_graph.edges_connecting(fun_index, fun_index).next() {
            let (self_edge, call) = (self_edge.id(), *self_edge.weight());
            let span = match call {
                CallKind::Direct(span) => span,
                _ => continue,
            };
            if function_data.is_pearlite {
                // Allow simple recursion in logic functions
                call_graph.remove_edge(self_edge);
                continue;
            }
            call_graph.remove_edge(self_edge);
            if !function_data.has_variant && def_id.is_local() {
                let fun_span = ctx.tcx.def_span(def_id);
                let mut error =
                    ctx.error(fun_span, "Recursive function without a `#[variant]` clause");
                error.span_note(span, "Recursive call happens here");
                error.emit();
            }
        };
        if let Some(loop_span) = function_data.has_loops {
            let fun_span = ctx.tcx.def_span(def_id);
            let mut error = if contracts_items::is_ghost_closure(ctx.tcx, def_id) {
                ctx.error(fun_span, "`ghost!` block must not contain loops.")
            } else {
                ctx.error(fun_span, "`#[terminates]` function must not contain loops.")
            };
            error.span_note(loop_span, "looping occurs here");
            error.emit();
        }
    }

    // detect mutual recursion
    let cycles = petgraph::algo::kosaraju_scc(&call_graph);
    for mut cycle in cycles {
        // find a root as a local function
        let Some(root_idx) = cycle.iter().position(|n| {
            let id = call_graph.node_weight(*n).unwrap().def_id();
            id.is_local() && ctx.def_kind(id).is_fn_like()
        }) else {
            continue;
        };
        let root = cycle.remove(root_idx);

        if cycle.is_empty() && call_graph.edges_connecting(root, root).count() == 0 {
            // Need more than 2 components.
            continue;
        }
        let in_cycle: IndexSet<_> = cycle.into_iter().collect();
        let mut cycle = Vec::new();
        // Build the cycle in the right order.
        petgraph::visit::depth_first_search(&call_graph, std::iter::once(root), |n| {
            use petgraph::visit::Control;
            match n {
                petgraph::visit::DfsEvent::Discover(n, _) => {
                    if in_cycle.contains(&n) {
                        cycle.push(n);
                        Control::Continue
                    } else if n == root {
                        Control::Continue
                    } else {
                        Control::Prune
                    }
                }
                petgraph::visit::DfsEvent::BackEdge(_, n) if n == root => Control::Break(()),
                _ => Control::Continue,
            }
        });

        let root_def_id = call_graph.node_weight(root).unwrap().def_id();
        let mut error = ctx.error(
            ctx.def_span(root_def_id),
            &format!(
                "Mutually recursive functions: when calling `{}`...",
                ctx.tcx.def_path_str(root_def_id)
            ),
        );
        let mut next_node = root;
        let mut current_node;
        for (idx, &node) in cycle.iter().chain(std::iter::once(&root)).enumerate() {
            current_node = next_node;
            next_node = node;
            let last = idx == cycle.len();
            if let Some(e) = call_graph.edges_connecting(current_node, next_node).next() {
                let call = *e.weight();
                let adverb = if last && cycle.len() >= 1 { "finally" } else { "then" };
                let punct = if last { "." } else { "..." };
                let f1 =
                    ctx.tcx.def_path_str(call_graph.node_weight(current_node).unwrap().def_id());
                let f2 = ctx.tcx.def_path_str(call_graph.node_weight(next_node).unwrap().def_id());

                match call {
                    CallKind::Direct(span) => {
                        error.span_note(span, format!("{adverb} `{f1}` calls `{f2}`{punct}"));
                    }
                    CallKind::Ghost => { /* skip the ghost call in the message */ }
                    CallKind::GenericBound(indirect_id, span) => {
                        let f3 = ctx.tcx.def_path_str(indirect_id);
                        error.span_note(
                            span,
                            format!(
                                "{adverb} `{f1}` might call `{f2}` via the call to `{f3}`{punct}"
                            ),
                        );
                    }
                }
            }
        }

        error.emit();
    }

    ctx.tcx.dcx().abort_if_errors();
}

struct CallGraph {
    graph: graph::DiGraph<GraphNode, CallKind>,
    additional_data: IndexMap<graph::NodeIndex, FunctionData>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum GraphNode {
    /// A normal function.
    Function(DefId),
    /// This node is used in the following case:
    /// ```
    /// # macro_rules! ignore { ($($t:tt)*) => {}; }
    /// # ignore! {
    /// trait Tr { // possibly in another crate
    ///     #[logic] #[open] fn f() { /* ... */ }
    /// }
    /// impl Tr {} // in the current crate
    /// # }
    /// ```
    /// In this case, we create an additional node in the graph, corresponding to the
    /// implementation of the default function.
    ///
    /// # Why though?
    ///
    /// First, this is sound, because it acts as if the function was actually written in
    /// the impl block (with the same definition as the default one).
    ///
    /// Then we feel this is justified to do this transformation, precisely because the
    /// default function is transparent at the point of the impl, so the user can 'see'
    /// its definition.
    ImplDefaultTransparent { default_function: DefId, impl_block: LocalDefId },
}
impl GraphNode {
    fn def_id(&self) -> DefId {
        match self {
            GraphNode::Function(def_id) => *def_id,
            GraphNode::ImplDefaultTransparent { default_function, .. } => *default_function,
        }
    }
}

#[derive(Default)]
struct BuildFunctionsGraph {
    graph: graph::DiGraph<GraphNode, CallKind>,
    additional_data: IndexMap<graph::NodeIndex, FunctionData>,
    graph_node_to_index: IndexMap<GraphNode, graph::NodeIndex>,
}

#[derive(Clone, Copy, Debug)]
enum CallKind {
    /// Call of a function.
    Direct(Span),
    /// Call of the closure inside a `ghost!` block.
    Ghost,
    /// 'Indirect' call, this is an egde going inside an `impl` block. This happens when
    /// calling a generic function while specializing a type. For example:
    /// ```rust
    /// fn f<T: Clone>() { /* ... */ }
    /// fn g() { f::<i32>(); } // arc from g to `i32::clone`
    /// ```
    ///
    /// The `DefId` is the one for the generic function, here `f`.
    GenericBound(DefId, Span),
}

#[derive(Debug)]
struct FunctionData {
    /// `true` if the function is a pearlite function (e.g. `#[logic]`).
    is_pearlite: bool,
    /// `true` if the function has a `#[variant]` annotation.
    ///
    /// For now, mutually recursive functions are never allowed, so this only matter for
    /// the simple recursion check.
    has_variant: bool,
    /// `Some` if the function contains a loop construct (contains the location of the loop).
    ///
    /// The body of external function are not visited, so this field will be `false`.
    has_loops: Option<Span>,
}

impl BuildFunctionsGraph {
    /// Insert a new node in the graph, or fetch an existing node id.
    fn insert_function(&mut self, tcx: TyCtxt, graph_node: GraphNode) -> graph::NodeIndex {
        let def_id = graph_node.def_id();
        match self.graph_node_to_index.entry(graph_node) {
            indexmap::map::Entry::Occupied(n) => *n.get(),
            indexmap::map::Entry::Vacant(entry) => {
                let node = self.graph.add_node(graph_node);
                self.additional_data.insert(
                    node,
                    FunctionData {
                        is_pearlite: contracts_items::is_pearlite(tcx, def_id),
                        has_variant: contracts_items::has_variant_clause(tcx, def_id),
                        has_loops: None,
                    },
                );
                entry.insert(node);
                node
            }
        }
    }

    /// Process the call from `node` to `called_id`.
    fn function_call<'tcx>(
        &mut self,
        tcx: TyCtxt<'tcx>,
        node: graph::NodeIndex,
        param_env: ParamEnv<'tcx>,
        called_id: DefId,
        generic_args: GenericArgsRef<'tcx>,
        call_span: Span,
    ) {
        let (called_id, generic_args) = if TraitResolved::is_trait_item(tcx, called_id) {
            match TraitResolved::resolve_item(tcx, param_env, called_id, generic_args) {
                TraitResolved::Instance(def_id, subst) => (def_id, subst),
                _ => (called_id, generic_args),
            }
        } else {
            (called_id, generic_args)
        };
        if contracts_items::is_ghost_from_fn(tcx, called_id) {
            // This is a `ghost!` call, so it needs special handling.
            let &[_, ty] = generic_args.as_slice() else {
                unreachable!();
            };
            let GenericArgKind::Type(ty) = ty.unpack() else { unreachable!() };
            let TyKind::Closure(ghost_def_id, _) = ty.kind() else { unreachable!() };

            let ghost_node = self.insert_function(tcx, GraphNode::Function(*ghost_def_id));
            self.graph.update_edge(node, ghost_node, CallKind::Ghost);
            return;
        }

        let (called_node, skip_self_bounds) = if TraitResolved::is_trait_item(tcx, called_id)
            && let Some(called_node) = TraitResolved::impl_id_of_trait(
                tcx,
                param_env,
                tcx.trait_of_item(called_id).unwrap(),
                generic_args,
            )
            .and_then(|id| {
                self.graph_node_to_index.get(&GraphNode::ImplDefaultTransparent {
                    default_function: called_id,
                    impl_block: id.as_local()?,
                })
            }) {
            (*called_node, true)
        } else {
            (self.insert_function(tcx, GraphNode::Function(called_id)), false)
        };
        self.graph.update_edge(node, called_node, CallKind::Direct(call_span));

        // Iterate over the trait bounds of the called function, and assume we call all functions of the corresponding trait if they are specialized.
        for bound in tcx.param_env(called_id).caller_bounds() {
            let Some(clause) = bound.as_trait_clause() else { continue };
            let clause = tcx.instantiate_bound_regions_with_erased(clause);
            let trait_ref = clause.trait_ref;
            let subst = trait_ref.args;
            let subst = EarlyBinder::bind(subst).instantiate(tcx, generic_args);

            match clause.self_ty().kind() {
                rustc_type_ir::TyKind::Param(ty) => {
                    if ty.index == 0 && skip_self_bounds {
                        // trait Tr {
                        //     #[logic] fn f<T: Tr>() {}
                        // }
                        // impl Tr for i32 {}
                        //
                        // #[logic] fn g<T: Tr>() {
                        //     <i32 as Tr>::f::<T>()
                        // }
                        //
                        // ==> T: Tr should appear in the bounds, but not Self: Tr.
                        // TODO: Is this only true for Self?
                        continue;
                    }
                }
                _ => {}
            }

            for &item in tcx.associated_item_def_ids(trait_ref.def_id) {
                let (item_id, _) = match TraitResolved::resolve_item(tcx, param_env, item, subst) {
                    TraitResolved::Instance(def_id, subst) => (def_id, subst),
                    _ => continue,
                };
                let item_node = self.insert_function(tcx, GraphNode::Function(item_id));
                self.graph.update_edge(
                    node,
                    item_node,
                    CallKind::GenericBound(called_id, call_span),
                );
            }
        }
    }
}

impl CallGraph {
    /// Build the call graph of all functions appearing in the current crate,
    /// exclusively for the purpose of termination checking.
    ///
    /// In particular, this means it only contains `#[terminates]` functions.
    fn build(ctx: &mut TranslationCtx) -> Self {
        let tcx = ctx.tcx;
        let mut build_call_graph = BuildFunctionsGraph::default();

        // Create the `GraphNode::ImplDefaultTransparent` nodes
        for (trait_id, impls) in tcx.all_local_trait_impls(()) {
            for &impl_id in impls {
                let items_in_impl = tcx.impl_item_implementor_ids(impl_id.to_def_id());
                for &item_id in tcx.associated_item_def_ids(trait_id) {
                    if items_in_impl.contains_key(&item_id) {
                        continue;
                    }
                    let is_transparent = ctx.is_transparent_from(
                        item_id,
                        tcx.parent_module_from_def_id(impl_id).to_def_id(),
                    );
                    if !is_transparent || !contracts_items::is_pearlite(tcx, item_id) {
                        continue;
                    }
                    build_call_graph.insert_function(
                        tcx,
                        GraphNode::ImplDefaultTransparent {
                            default_function: item_id,
                            impl_block: impl_id,
                        },
                    );
                }
            }
        }

        for (graph_node, node) in build_call_graph.graph_node_to_index.clone() {
            let GraphNode::ImplDefaultTransparent { default_function: item_id, impl_block: _ } =
                graph_node
            else {
                continue;
            };

            let param_env = tcx.param_env(item_id);
            let term = ctx.term(item_id).unwrap();
            let mut visitor = TermCalls { results: IndexSet::new() };
            visitor.visit_term(term);

            for (called_id, generic_args, call_span) in visitor.results {
                // FIXME: weird, why does taking the param_env/generic_args of item_id (aka the function in the *trait*, not the one specialized in the *impl*) works?
                // This may not be sound.
                build_call_graph.function_call(
                    tcx,
                    node,
                    param_env,
                    called_id,
                    generic_args,
                    call_span,
                );
            }
        }

        for local_id in ctx.hir().body_owners() {
            if !(contracts_items::is_pearlite(ctx.tcx, local_id.to_def_id())
                || contract_of(ctx, local_id.to_def_id()).terminates)
            {
                // Only consider functions marked with `terminates`: we already ensured that a `terminates` functions only calls other `terminates` functions.
                continue;
            }
            let def_id = local_id.to_def_id();
            let node = build_call_graph.insert_function(ctx.tcx, GraphNode::Function(def_id));

            if is_trusted_function(ctx.tcx, def_id)
                || contracts_items::is_no_translate(ctx.tcx, def_id)
            {
                // Cut all arcs from this function.
                continue;
            }

            let param_env = ctx.tcx.param_env(def_id);
            let (thir, expr) = ctx.thir_body(local_id).unwrap();
            let thir = thir.borrow();
            // Collect functions called by this function
            let mut visitor =
                FunctionCalls { thir: &thir, tcx, calls: IndexSet::new(), has_loops: None };
            <FunctionCalls as thir::visit::Visitor>::visit_expr(&mut visitor, &thir[expr]);

            build_call_graph.additional_data[&node].has_loops = visitor.has_loops;

            for (called_id, generic_args, call_span) in visitor.calls {
                build_call_graph.function_call(
                    tcx,
                    node,
                    param_env,
                    called_id,
                    generic_args,
                    call_span,
                );
            }
        }

        Self { graph: build_call_graph.graph, additional_data: build_call_graph.additional_data }
    }
}

/// Gather the functions calls that appear in a particular function, and store them in `calls`.
struct FunctionCalls<'thir, 'tcx> {
    thir: &'thir thir::Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// Contains:
    /// - The id of the _called_ function.
    /// - The generic args for this call.
    /// - The span of the call (for error messages).
    calls: IndexSet<(DefId, &'tcx GenericArgs<'tcx>, Span)>,
    /// `Some` if the function contains a loop construct.
    has_loops: Option<Span>,
}

impl<'thir, 'tcx> thir::visit::Visitor<'thir, 'tcx> for FunctionCalls<'thir, 'tcx> {
    fn thir(&self) -> &'thir thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Call { fun, fn_span, .. } => {
                if let &FnDef(def_id, generic_args) = self.thir[fun].ty.kind() {
                    self.calls.insert((def_id, generic_args, fn_span));
                }
            }
            thir::ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                let (thir, expr) = self.tcx.thir_body(closure_id).unwrap_or_else(|_| {
                    crate::error::Error::from(crate::error::InternalError("Cannot fetch THIR body"))
                        .emit(self.tcx)
                });
                let thir = thir.borrow();

                let mut closure_visitor = FunctionCalls {
                    thir: &thir,
                    tcx: self.tcx,
                    calls: std::mem::take(&mut self.calls),
                    has_loops: None,
                };
                thir::visit::walk_expr(&mut closure_visitor, &thir[expr]);
                self.calls.extend(closure_visitor.calls);
                self.has_loops = self.has_loops.or(closure_visitor.has_loops);
            }
            thir::ExprKind::Loop { .. } => self.has_loops = Some(expr.span),
            _ => {}
        }
        thir::visit::walk_expr(self, expr);
    }
}

struct TermCalls<'tcx> {
    results: IndexSet<(DefId, &'tcx GenericArgs<'tcx>, Span)>,
}

impl<'tcx> TermVisitor<'tcx> for TermCalls<'tcx> {
    fn visit_term(&mut self, term: &crate::pearlite::Term<'tcx>) {
        crate::pearlite::super_visit_term(term, self);
        if let TermKind::Call { id, subst, args: _ } = &term.kind {
            self.results.insert((*id, subst, term.span));
        }
    }
}
