//! Detection of loops and mutually recursive functions.
//!
//! Care is taken around the interaction with traits, like the following example:
//! ```ignore
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
//!
//! # Default function
//!
//! Default function in traits, as well as `impl` blocks marked with `default`, are
//! special-cased when handling logical functions: see the documentation in
//! [`ImplDefaultTransparent`] for more details.

use crate::{
    backend::is_trusted_item,
    contracts_items::{has_variant_clause, is_no_translate, is_pearlite},
    ctx::TranslationCtx,
    error::CannotFetchThir,
    pearlite::{TermKind, TermVisitor},
    specification::contract_of,
    traits::TraitResolved,
    util::erased_identity_for_item,
};
use indexmap::{IndexMap, IndexSet};
use petgraph::{
    algo::tarjan_scc,
    graph,
    visit::{Control, DfsEvent, EdgeRef as _, depth_first_search},
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::{infer::TyCtxtInferExt as _, traits::ObligationCause};
use rustc_middle::{
    thir,
    ty::{Clauses, EarlyBinder, FnDef, GenericArgs, GenericArgsRef, TyCtxt, TypingEnv, TypingMode},
};
use rustc_span::Span;
use rustc_trait_selection::traits::normalize_param_env_or_error;

/// Validate that a `#[terminates]` function cannot loop indefinitely. This includes:
/// - forbidding program function from using loops of any kind (this should be relaxed
///   later).
/// - forbidding (mutual) recursive calls, especially when traits are involved.
///
/// Note that for logical functions, these are relaxed: we don't check loops, nor simple
/// recursion, because why3 will handle it for us.
pub(crate) fn validate_terminates(ctx: &TranslationCtx) -> Result<(), CannotFetchThir> {
    ctx.tcx.dcx().abort_if_errors(); // There may have been errors before, if a `#[terminates]` calls a non-`#[terminates]`.

    let CallGraph { graph: mut call_graph, additional_data, loops_in_ghost } =
        CallGraph::build(ctx)?;

    for loop_in_ghost in loops_in_ghost {
        ctx.error(loop_in_ghost, "`ghost!` blocks must not contain loops.").emit();
    }

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
            let mut error = ctx.error(fun_span, "`#[terminates]` function must not contain loops.");
            error.span_note(loop_span, "looping occurs here");
            error.emit();
        }
    }

    // detect mutual recursion
    let cycles = tarjan_scc(&call_graph);
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
        depth_first_search(&call_graph, [root], |n| match n {
            DfsEvent::Discover(n, _) => {
                if in_cycle.contains(&n) {
                    cycle.push(n);
                    Control::Continue
                } else if n == root {
                    Control::Continue
                } else {
                    Control::Prune
                }
            }
            DfsEvent::BackEdge(_, n) if n == root => Control::Break(()),
            _ => Control::Continue,
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
        for (idx, &node) in cycle.iter().chain([&root]).enumerate() {
            current_node = next_node;
            next_node = node;
            let last = idx == cycle.len();
            if let Some(e) = call_graph.edges_connecting(current_node, next_node).next() {
                let call = *e.weight();
                let adverb = if last && !cycle.is_empty() { "finally" } else { "then" };
                let punct = if last { "." } else { "..." };
                let f1 =
                    ctx.tcx.def_path_str(call_graph.node_weight(current_node).unwrap().def_id());
                let f2 = ctx.tcx.def_path_str(call_graph.node_weight(next_node).unwrap().def_id());

                match call {
                    CallKind::Direct(span) => {
                        error.span_note(span, format!("{adverb} `{f1}` calls `{f2}`{punct}"));
                    }
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
    Ok(())
}

struct CallGraph {
    graph: graph::DiGraph<GraphNode, CallKind>,
    additional_data: IndexMap<graph::NodeIndex, FunctionData>,
    loops_in_ghost: Vec<Span>,
}

#[derive(Default)]
struct BuildFunctionsGraph<'tcx> {
    graph: graph::DiGraph<GraphNode, CallKind>,
    additional_data: IndexMap<graph::NodeIndex, FunctionData>,
    graph_node_to_index: IndexMap<GraphNode, graph::NodeIndex>,
    /// Stores the generic bounds that are left when instantiating the default method in
    /// the impl block.
    ///
    /// This is used to retrieve all the bounds when calling this function.
    default_functions_bounds: IndexMap<graph::NodeIndex, Clauses<'tcx>>,
    is_default_function: IndexSet<DefId>,
    visited_default_specialization: IndexSet<graph::NodeIndex>,
    specialization_nodes:
        IndexMap<graph::NodeIndex, rustc_infer::traits::specialization_graph::LeafDef>,
}

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ImplDefaultTransparent {
    /// The default implementation selected for the impl block.
    default_function: DefId,
    impl_block: LocalDefId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum GraphNode {
    /// A normal function.
    Function(DefId),

    ImplDefaultTransparent(ImplDefaultTransparent),
}
impl GraphNode {
    fn def_id(&self) -> DefId {
        match self {
            GraphNode::Function(def_id) => *def_id,
            GraphNode::ImplDefaultTransparent(ImplDefaultTransparent {
                default_function, ..
            }) => *default_function,
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum CallKind {
    /// Call of a function.
    Direct(Span),
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

impl<'tcx> BuildFunctionsGraph<'tcx> {
    /// Insert a new node in the graph, or fetch an existing node id.
    fn insert_function(&mut self, tcx: TyCtxt, graph_node: GraphNode) -> graph::NodeIndex {
        let def_id = graph_node.def_id();
        match self.graph_node_to_index.entry(graph_node) {
            indexmap::map::Entry::Occupied(n) => *n.get(),
            indexmap::map::Entry::Vacant(entry) => {
                let node = self.graph.add_node(graph_node);
                self.additional_data.insert(node, FunctionData {
                    is_pearlite: is_pearlite(tcx, def_id),
                    has_variant: has_variant_clause(tcx, def_id),
                    has_loops: None,
                });
                entry.insert(node);
                node
            }
        }
    }

    /// Process the call from `node` to `called_id`.
    fn function_call(
        &mut self,
        ctx: &TranslationCtx<'tcx>,
        node: graph::NodeIndex,
        typing_env: TypingEnv<'tcx>,
        called_id: DefId,
        generic_args: GenericArgsRef<'tcx>,
        call_span: Span,
    ) -> Result<(), CannotFetchThir> {
        let tcx = ctx.tcx;
        let (called_id, generic_args) = if TraitResolved::is_trait_item(tcx, called_id) {
            match TraitResolved::resolve_item(tcx, typing_env, called_id, generic_args) {
                TraitResolved::Instance(def_id, subst) => (def_id, subst),
                _ => (called_id, generic_args),
            }
        } else {
            (called_id, generic_args)
        };

        // TODO: this code is kind of a soup, rework or refactor into a function
        let (called_node, bounds, impl_self_bound) = 'bl: {
            // this checks if we are calling a function with a default implementation,
            // as processed at the beginning of `CallGraph::build`.
            'not_default: {
                if !self.is_default_function.contains(&called_id) {
                    break 'not_default;
                };
                let trait_id = match tcx.impl_of_method(called_id) {
                    Some(id) => {
                        if let Some(trait_id) = tcx.trait_id_of_impl(id) {
                            trait_id
                        } else {
                            break 'not_default;
                        }
                    }
                    None => {
                        if let Some(trait_id) = tcx.trait_of_item(called_id) {
                            trait_id
                        } else {
                            break 'not_default;
                        }
                    }
                };
                let Some(spec_impl_id) =
                    TraitResolved::impl_id_of_trait(tcx, typing_env, trait_id, generic_args)
                        .and_then(|id| id.as_local())
                else {
                    break 'not_default;
                };
                let default_node = ImplDefaultTransparent {
                    default_function: called_id,
                    impl_block: spec_impl_id,
                };
                let Some(node) = self.visit_specialized_default_function(ctx, default_node)? else {
                    break 'not_default;
                };
                let bounds = self.default_functions_bounds[&node];
                let self_bound = tcx.impl_trait_header(spec_impl_id);
                break 'bl (node, bounds, self_bound);
            }
            (
                self.insert_function(tcx, GraphNode::Function(called_id)),
                tcx.param_env(called_id).caller_bounds(),
                None,
            )
        };
        self.graph.update_edge(node, called_node, CallKind::Direct(call_span));

        // Iterate over the trait bounds of the called function, and assume we call all functions of the corresponding trait if they are specialized.
        for bound in bounds {
            let Some(clause) = bound.as_trait_clause() else { continue };
            let clause = tcx.instantiate_bound_regions_with_erased(clause);
            let trait_ref = clause.trait_ref;
            if let Some(self_bound) = &impl_self_bound {
                if trait_ref == self_bound.trait_ref.instantiate_identity() {
                    continue;
                }
            }

            let subst = EarlyBinder::bind(trait_ref.args).instantiate(tcx, generic_args);
            for &item in tcx.associated_item_def_ids(trait_ref.def_id) {
                let TraitResolved::Instance(item_id, _) =
                    TraitResolved::resolve_item(tcx, typing_env, item, subst)
                else {
                    continue;
                };
                let item_node = self.insert_function(tcx, GraphNode::Function(item_id));
                self.graph.update_edge(
                    node,
                    item_node,
                    CallKind::GenericBound(called_id, call_span),
                );
            }
        }
        Ok(())
    }

    /// This visit the special function that is called when calling:
    /// - a default function in a trait (or in a default impl)
    /// - that is logical
    /// - and visible at the point of implementation, that is
    ///   ```ignore
    ///   trait Tr {
    ///       #[logic] #[open(self)] fn f() {}
    ///   }
    ///   impl Tr for i32 { }
    ///   #[logic] #[open(self)] fn g() { <i32 as Tr>::f(); }
    ///   ```
    ///   Here the implementation `<i32 as Tr>` generates an additional node in the
    ///   termination graph, which is "`f` but specialized in `impl Tr for i32`".
    ///
    /// We use this function, so that only those specialization that are actually called are visited.
    fn visit_specialized_default_function(
        &mut self,
        ctx: &TranslationCtx<'tcx>,
        graph_node: ImplDefaultTransparent,
    ) -> Result<Option<graph::NodeIndex>, CannotFetchThir> {
        let Some(&node) =
            self.graph_node_to_index.get(&GraphNode::ImplDefaultTransparent(graph_node))
        else {
            return Ok(None);
        };
        if !self.visited_default_specialization.insert(node) {
            return Ok(Some(node));
        }
        let tcx = ctx.tcx;
        let ImplDefaultTransparent { default_function: item_id, impl_block: impl_id } = graph_node;
        let specialization_node = &self.specialization_nodes[&node];

        let impl_id = impl_id.to_def_id();
        let typing_env = ctx.typing_env(impl_id);
        let term = ctx.term(item_id)?.unwrap();
        let mut visitor = TermCalls { results: IndexSet::new() };
        visitor.visit_term(term);

        let trait_id = tcx.trait_id_of_impl(impl_id).unwrap();

        // translate the args of the impl to match the trait.
        let infcx = tcx.infer_ctxt().build(TypingMode::non_body_analysis());
        let impl_args = rustc_trait_selection::traits::translate_args(
            &infcx,
            typing_env.param_env,
            impl_id,
            erased_identity_for_item(tcx, impl_id),
            specialization_node.defining_node,
        );

        // Take the generic arguments of the default function, instantiated with
        // the type parameters from the impl block.
        let func_impl_args =
            erased_identity_for_item(tcx, item_id).rebase_onto(tcx, trait_id, impl_args);

        // data for when we call this function
        let item_typing_env = ctx.typing_env(item_id);
        let item_typing_env = EarlyBinder::bind(item_typing_env).instantiate(tcx, func_impl_args);
        let bounds =
            normalize_param_env_or_error(tcx, item_typing_env.param_env, ObligationCause::dummy())
                .caller_bounds();
        self.default_functions_bounds.insert(node, bounds);

        for (called_id, generic_args, call_span) in visitor.results {
            // Instantiate the args for the call with the context we just built up.
            let actual_args = tcx.instantiate_and_normalize_erasing_regions(
                func_impl_args,
                item_typing_env,
                EarlyBinder::bind(generic_args),
            );

            self.function_call(ctx, node, typing_env, called_id, actual_args, call_span)?;
        }
        Ok(Some(node))
    }
}

impl CallGraph {
    /// Build the call graph of all functions appearing in the current crate,
    /// exclusively for the purpose of termination checking.
    ///
    /// In particular, this means it only contains `#[terminates]` functions.
    fn build(ctx: &TranslationCtx) -> Result<Self, CannotFetchThir> {
        let tcx = ctx.tcx;
        let mut build_call_graph = BuildFunctionsGraph::default();

        // Create the `GraphNode::ImplDefaultTransparent` nodes.
        for (trait_id, impls) in tcx.all_local_trait_impls(()) {
            for &impl_local_id in impls {
                let module_id = tcx.parent_module_from_def_id(impl_local_id).to_def_id();
                let impl_id = impl_local_id.to_def_id();
                let items_in_impl = tcx.impl_item_implementor_ids(impl_id);

                for &item_id in tcx.associated_item_def_ids(trait_id) {
                    if items_in_impl.contains_key(&item_id) {
                        // The function is explicitely implemented, skip
                        continue;
                    }

                    let default_item = {
                        let trait_def = tcx.trait_def(trait_id);
                        let leaf_def = trait_def
                            .ancestors(tcx, impl_id)
                            .unwrap()
                            .leaf_def(tcx, item_id)
                            .unwrap_or_else(|| {
                                unreachable!(
                                    "no definition found for item {} in impl {}",
                                    tcx.def_path_str(item_id),
                                    tcx.def_path_str(impl_id)
                                );
                            });
                        leaf_def
                    };
                    let default_item_id = default_item.item.def_id;

                    let is_transparent = ctx.is_transparent_from(default_item_id, module_id);
                    if !is_transparent || !is_pearlite(tcx, default_item_id) {
                        // only consider item that are:
                        // - transparent from the POV of the impl block
                        // - logical items
                        continue;
                    }

                    let node = build_call_graph.insert_function(
                        tcx,
                        GraphNode::ImplDefaultTransparent(ImplDefaultTransparent {
                            default_function: default_item_id,
                            impl_block: impl_local_id,
                        }),
                    );
                    build_call_graph.specialization_nodes.insert(node, default_item);
                    build_call_graph.is_default_function.insert(default_item_id);
                }
            }
        }

        let mut loops_in_ghost = Vec::new();

        for local_id in ctx.hir().body_owners() {
            let def_id = local_id.to_def_id();
            if is_trusted_item(ctx.tcx, def_id) || is_no_translate(ctx.tcx, def_id) {
                continue;
            }
            let (thir, expr) = ctx.thir_body(local_id).unwrap();
            let thir = thir.borrow();
            let mut visitor = GhostLoops {
                thir: &thir,
                tcx,
                thir_failed: false,
                loops_in_ghost: Vec::new(),
                is_in_ghost: false,
            };
            <GhostLoops as thir::visit::Visitor>::visit_expr(&mut visitor, &thir[expr]);
            loops_in_ghost.extend(visitor.loops_in_ghost);
        }

        for local_id in ctx.hir().body_owners() {
            if !(is_pearlite(ctx.tcx, local_id.to_def_id())
                || contract_of(ctx, local_id.to_def_id()).terminates)
            {
                // Only consider functions marked with `terminates`: we already ensured that a `terminates` functions only calls other `terminates` functions.
                continue;
            }
            let def_id = local_id.to_def_id();
            let node = build_call_graph.insert_function(ctx.tcx, GraphNode::Function(def_id));

            if is_trusted_item(ctx.tcx, def_id) || is_no_translate(ctx.tcx, def_id) {
                // Cut all arcs from this function.
                continue;
            }

            let typing_env = ctx.typing_env(def_id);
            let (thir, expr) = ctx.thir_body(local_id).unwrap();
            let thir = thir.borrow();
            // Collect functions called by this function
            let mut visitor = FunctionCalls {
                thir: &thir,
                tcx,
                calls: IndexSet::new(),
                has_loops: None,
                thir_failed: false,
            };
            <FunctionCalls as thir::visit::Visitor>::visit_expr(&mut visitor, &thir[expr]);

            if visitor.thir_failed {
                return Err(CannotFetchThir);
            }

            build_call_graph.additional_data[&node].has_loops = visitor.has_loops;

            for (called_id, generic_args, call_span) in visitor.calls {
                build_call_graph.function_call(
                    ctx,
                    node,
                    typing_env,
                    called_id,
                    generic_args,
                    call_span,
                )?;
            }
        }

        Ok(Self {
            graph: build_call_graph.graph,
            additional_data: build_call_graph.additional_data,
            loops_in_ghost,
        })
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
    /// If `true`, we should error with a [`CannotFetchThir`] error.
    thir_failed: bool,
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
                let Ok((thir, expr)) = self.tcx.thir_body(closure_id) else {
                    self.thir_failed = true;
                    return;
                };
                let thir = thir.borrow();

                let mut closure_visitor = FunctionCalls {
                    thir: &thir,
                    tcx: self.tcx,
                    calls: std::mem::take(&mut self.calls),
                    has_loops: None,
                    thir_failed: false,
                };
                thir::visit::walk_expr(&mut closure_visitor, &thir[expr]);
                if closure_visitor.thir_failed {
                    self.thir_failed = true;
                    return;
                }
                self.calls.extend(closure_visitor.calls);
                self.has_loops = self.has_loops.or(closure_visitor.has_loops);
            }
            thir::ExprKind::Loop { .. } => {
                self.has_loops = Some(expr.span);
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr);
    }
}

/// Gather the loops in `ghost!` code for a given function.
struct GhostLoops<'thir, 'tcx> {
    thir: &'thir thir::Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// loop constructs in ghost code are forbidden for now.
    loops_in_ghost: Vec<Span>,
    is_in_ghost: bool,
    /// If `true`, we should error with a [`CannotFetchThir`] error.
    thir_failed: bool,
}

impl<'thir, 'tcx> thir::visit::Visitor<'thir, 'tcx> for GhostLoops<'thir, 'tcx> {
    fn thir(&self) -> &'thir thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                let Ok((thir, expr)) = self.tcx.thir_body(closure_id) else {
                    self.thir_failed = true;
                    return;
                };
                let thir = thir.borrow();

                let mut closure_visitor = GhostLoops {
                    thir: &thir,
                    tcx: self.tcx,
                    loops_in_ghost: Vec::new(),
                    is_in_ghost: self.is_in_ghost,
                    thir_failed: false,
                };
                thir::visit::walk_expr(&mut closure_visitor, &thir[expr]);
                if closure_visitor.thir_failed {
                    self.thir_failed = true;
                    return;
                }
                self.loops_in_ghost.extend(closure_visitor.loops_in_ghost);
            }
            thir::ExprKind::Loop { .. } => {
                if self.is_in_ghost {
                    self.loops_in_ghost.push(expr.span);
                }
            }
            thir::ExprKind::Scope {
                region_scope: _,
                lint_level: thir::LintLevel::Explicit(hir_id),
                value: _,
            } => {
                if super::is_ghost_block(self.tcx, hir_id) {
                    let old_is_ghost = std::mem::replace(&mut self.is_in_ghost, true);
                    thir::visit::walk_expr(self, expr);
                    self.is_in_ghost = old_is_ghost;
                    return;
                }
            }
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
