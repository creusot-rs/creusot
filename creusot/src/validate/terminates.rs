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

use std::iter::repeat;

use crate::{
    backend::is_trusted_item,
    contracts_items::{has_variant_clause, is_no_translate, is_pearlite},
    ctx::TranslationCtx,
    translation::{
        pearlite::{Term, TermKind, TermVisitor, super_visit_term},
        traits::{Instance, TraitResolved},
    },
    util::erased_identity_for_item,
};
use indexmap::{IndexMap, IndexSet};
use petgraph::{
    algo::tarjan_scc,
    graph,
    visit::{Control, DfsEvent, EdgeRef as _, depth_first_search},
};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_infer::{
    infer::TyCtxtInferExt as _,
    traits::{ImplSource, ObligationCause},
};
use rustc_middle::{
    thir::{self, visit::Visitor},
    ty::{Clauses, EarlyBinder, FnDef, GenericArgs, GenericArgsRef, TypingEnv, TypingMode},
};
use rustc_span::Span;
use rustc_trait_selection::traits::{normalize_param_env_or_error, specialization_graph};

/// Validate that a `#[terminates]` function cannot loop indefinitely. This includes:
/// - forbidding program function from using loops of any kind (this should be relaxed
///   later).
/// - forbidding (mutual) recursive calls, especially when traits are involved.
///
/// Note that for logical functions, these are relaxed: we don't check loops, nor simple
/// recursion, because why3 will handle it for us.
pub(crate) fn validate_terminates(ctx: &TranslationCtx) {
    // Check for ghost loops
    for local_id in ctx.hir().body_owners() {
        let def_id = local_id.to_def_id();
        if is_trusted_item(ctx.tcx, def_id) || is_no_translate(ctx.tcx, def_id) {
            continue;
        }
        let (thir, expr) = ctx.get_thir(local_id).unwrap();
        let mut visitor = GhostLoops { thir: &thir, ctx, is_in_ghost: false };
        visitor.visit_expr(&thir[expr]);
    }

    let CallGraph { graph: mut call_graph } = CallGraph::build(ctx);

    // Detect simple recursion
    for fun_index in call_graph.node_indices() {
        let def_id = call_graph.node_weight(fun_index).unwrap().def_id();
        if let Some(self_edge) = call_graph.edges_connecting(fun_index, fun_index).next() {
            let (self_edge, call) = (self_edge.id(), *self_edge.weight());
            let CallKind::Direct(span) = call else { continue };
            call_graph.remove_edge(self_edge);
            if is_pearlite(ctx.tcx, def_id) {
                // Allow simple recursion in logic functions
                continue;
            }
            if !has_variant_clause(ctx.tcx, def_id) && def_id.is_local() {
                let fun_span = ctx.def_span(def_id);
                let mut error =
                    ctx.error(fun_span, "Recursive function without a `#[variant]` clause");
                error.span_note(span, "Recursive call happens here");
                error.emit();
            }
        };
    }

    // detect mutual recursion
    let cycles = tarjan_scc(&call_graph);
    for cycle in cycles {
        // find a root as a local function
        let Some(root_idx) = cycle.iter().position(|n| {
            let id = call_graph.node_weight(*n).unwrap().def_id();
            id.is_local() && ctx.def_kind(id).is_fn_like()
        }) else {
            continue;
        };
        let root = cycle[root_idx];

        if cycle.len() == 1 && call_graph.edges_connecting(root, root).count() == 0 {
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
                ctx.def_path_str(root_def_id)
            ),
        );
        let mut next_node = root;
        let mut current_node;
        assert!(cycle[0] == root);
        for (&node, last) in cycle.iter().skip(1).zip(repeat(false)).chain([(&root, true)]) {
            current_node = next_node;
            next_node = node;
            if let Some(e) = call_graph.edges_connecting(current_node, next_node).next() {
                let call = *e.weight();
                let adverb = if last && cycle.len() > 1 { "finally" } else { "then" };
                let punct = if last { "." } else { "..." };
                let f1 = ctx.def_path_str(call_graph.node_weight(current_node).unwrap().def_id());
                let f2 = ctx.def_path_str(call_graph.node_weight(next_node).unwrap().def_id());

                match call {
                    CallKind::Direct(span) => {
                        error.span_note(span, format!("{adverb} `{f1}` calls `{f2}`{punct}"));
                    }
                    CallKind::GenericBound(indirect_id, span) => {
                        let f3 = ctx.def_path_str(indirect_id);
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
    ctx.dcx().abort_if_errors();
}

struct CallGraph {
    graph: graph::DiGraph<GraphNode, CallKind>,
}

#[derive(Default)]
struct BuildFunctionsGraph<'tcx> {
    graph: graph::DiGraph<GraphNode, CallKind>,
    graph_node_to_index: IndexMap<GraphNode, graph::NodeIndex>,
    /// Stores the generic bounds that are left when instantiating the default method in
    /// the impl block.
    ///
    /// This is used to retrieve all the bounds when calling this function.
    default_functions_bounds: IndexMap<graph::NodeIndex, Clauses<'tcx>>,
}

/// This node is used in the following case:
/// ```
/// # macro_rules! ignore { ($($t:tt)*) => {}; }
/// # ignore! {
/// trait Tr { // possibly in another crate
///     #[logic] #[open] fn f() { /* ... */ }
/// }
/// impl Tr for Ty {} // in the current crate
/// # }
/// ```
/// In this case, we create an additional node in the graph, corresponding to the
/// instantiation of the default function for this impl block.
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
    item_id: DefId,
    impl_id: LocalDefId,
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
            GraphNode::ImplDefaultTransparent(ImplDefaultTransparent { item_id, .. }) => *item_id,
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

impl<'tcx> BuildFunctionsGraph<'tcx> {
    /// Insert a new node in the graph, or fetch an existing node id.
    fn insert_function(&mut self, graph_node: GraphNode) -> graph::NodeIndex {
        *self
            .graph_node_to_index
            .entry(graph_node)
            .or_insert_with(|| self.graph.add_node(graph_node))
    }

    /// Process the call from `node` to `called_id`.
    fn function_call(
        &mut self,
        ctx: &TranslationCtx<'tcx>,
        node: graph::NodeIndex,
        typing_env: TypingEnv<'tcx>,
        mut called_id: DefId,
        mut generic_args: GenericArgsRef<'tcx>,
        call_span: Span,
    ) {
        let res = TraitResolved::resolve_item(ctx.tcx, typing_env, called_id, generic_args);

        let (called_node, bounds, impl_self_bound);

        // If we are calling a known method, and this method has been defined in an ancestor of the impl
        // we found, and this method is logic and transparent from this impl and this impl is local, then use a
        // specialized default node
        if let TraitResolved::Instance(Instance { def, impl_ : Some(impl_)}) = res &&
            ctx.impl_of_method(def.0) != Some(impl_.0) && // The method is defined in an ancestor
            is_pearlite(ctx.tcx, def.0) && // The method is logic
            let Some(impl_ldid) = impl_.0.as_local() && // The impl is local
            ctx.is_transparent_from(def.0, ctx.parent_module_from_def_id(impl_ldid).to_def_id())
        {
            (called_id, generic_args) = def;
            (called_node, bounds) = self.visit_specialized_default_function(ctx, impl_ldid, def.0);
            impl_self_bound = Some(ctx.impl_trait_header(impl_.0).unwrap());
        } else {
            (called_id, generic_args) = res.to_opt(called_id, generic_args).unwrap();
            called_node = self.insert_function(GraphNode::Function(called_id));
            bounds = ctx.param_env(called_id).caller_bounds();
            impl_self_bound = None;
        }
        self.graph.update_edge(node, called_node, CallKind::Direct(call_span));

        // Iterate over the trait bounds of the called function, and assume we call all functions
        // of the corresponding trait if they are specialized.
        for bound in bounds {
            let Some(clause) = bound.as_trait_clause() else { continue };
            let clause = ctx.instantiate_bound_regions_with_erased(clause);
            let trait_ref = clause.trait_ref;
            if let Some(self_bound) = &impl_self_bound
                && trait_ref == self_bound.trait_ref.instantiate_identity()
            {
                continue;
            }

            let trait_ref = EarlyBinder::bind(trait_ref).instantiate(ctx.tcx, generic_args);
            let trait_ref = ctx.normalize_erasing_regions(typing_env, trait_ref);

            // FIXME: in the case of an ambiguity, `codegen_select_candidate` may return an error,
            // which makes the unwrap bellow fail. So this is not the entry point of the trait solver we want.
            // We want something that gives one possible instance, even if there are several instances
            // available.
            //
            // FIXME: this only handle the primary goal of the proof tree. We need to handle all the instances
            // used by this trait solving, including those that are used indirectly.
            if let ImplSource::Param(_) =
                ctx.codegen_select_candidate(typing_env.as_query_input(trait_ref)).unwrap()
            {
                continue;
            }

            for &item in ctx.associated_item_def_ids(trait_ref.def_id) {
                let TraitResolved::Instance(Instance { def: (item_id, _), .. }) =
                    TraitResolved::resolve_item(ctx.tcx, typing_env, item, trait_ref.args)
                else {
                    continue;
                };
                let item_node = self.insert_function(GraphNode::Function(item_id));
                self.graph.update_edge(
                    node,
                    item_node,
                    CallKind::GenericBound(called_id, call_span),
                );
            }
        }
    }

    /// This visits the special function that is called when calling:
    /// - a default function in a trait (or in a default impl)
    /// - that is logical
    /// - and visible at the point of implementation, that is
    ///   ```ignore
    ///   trait Tr {
    ///       #[logic] fn f() {}
    ///   }
    ///   impl Tr for i32 { }
    ///   #[logic] fn g() { <i32 as Tr>::f(); }
    ///   ```
    ///   Here the implementation `<i32 as Tr>` generates an additional node in the
    ///   termination graph, which is "`f` but specialized in `impl Tr for i32`".
    ///
    /// We use this function, so that only those specialization that are actually called are visited.
    ///
    /// # Returns
    ///
    /// - `None` if the conditions outlined earlier are not fulfilled
    /// - `Some(id)` else, where `id` is the index of the new specialized node in the graph.
    fn visit_specialized_default_function(
        &mut self,
        ctx: &TranslationCtx<'tcx>,
        impl_id: LocalDefId,
        item_id: DefId,
    ) -> (graph::NodeIndex, Clauses<'tcx>) {
        let node =
            self.insert_function(GraphNode::ImplDefaultTransparent(ImplDefaultTransparent {
                item_id,
                impl_id,
            }));
        if let Some(bounds) = self.default_functions_bounds.get(&node) {
            return (node, bounds);
        }

        let trait_id = ctx.trait_id_of_impl(impl_id.into()).unwrap();

        let spec_node_def = if let Some(def_impl) = ctx.impl_of_method(item_id) {
            specialization_graph::Node::Impl(def_impl)
        } else {
            specialization_graph::Node::Trait(trait_id)
        };

        // translate the args of the impl to match the trait.
        let infcx = ctx.infer_ctxt().build(TypingMode::non_body_analysis());
        let impl_args = rustc_trait_selection::traits::translate_args(
            &infcx,
            ctx.param_env(impl_id.into()),
            impl_id.into(),
            erased_identity_for_item(ctx.tcx, impl_id.into()),
            spec_node_def,
        );

        // Take the generic arguments of the default function, instantiated with
        // the type parameters from the impl block.
        let func_impl_args =
            erased_identity_for_item(ctx.tcx, item_id).rebase_onto(ctx.tcx, trait_id, impl_args);

        // data for when we call this function
        let param_env =
            EarlyBinder::bind(ctx.param_env(item_id)).instantiate(ctx.tcx, func_impl_args);
        let param_env = normalize_param_env_or_error(ctx.tcx, param_env, ObligationCause::dummy());
        let typing_env = TypingEnv { param_env, ..ctx.typing_env(item_id) };

        let bounds = param_env.caller_bounds();
        self.default_functions_bounds.insert(node, bounds);

        let mut visitor = TermCalls { results: IndexSet::new() };
        visitor.visit_term(&ctx.term(item_id).unwrap().1);
        for (called_id, generic_args, call_span) in visitor.results {
            // Instantiate the args for the call with the context we just built up.
            let actual_args = ctx.instantiate_and_normalize_erasing_regions(
                func_impl_args,
                typing_env,
                EarlyBinder::bind(generic_args),
            );

            self.function_call(ctx, node, typing_env, called_id, actual_args, call_span);
        }
        (node, bounds)
    }
}

impl CallGraph {
    /// Build the call graph of all functions appearing in the current crate,
    /// exclusively for the purpose of termination checking.
    ///
    /// In particular, this means it only contains `#[terminates]` functions.
    fn build(ctx: &TranslationCtx) -> Self {
        let mut build_call_graph = BuildFunctionsGraph::default();

        for local_id in ctx.hir().body_owners() {
            let def_id = local_id.to_def_id();
            if !(is_pearlite(ctx.tcx, def_id) || ctx.sig(def_id).contract.terminates) {
                // Only consider functions marked with `terminates`: we already ensured
                // that a `terminates` functions only calls other `terminates` functions.
                continue;
            }
            let node = build_call_graph.insert_function(GraphNode::Function(def_id));

            if is_trusted_item(ctx.tcx, def_id) || is_no_translate(ctx.tcx, def_id) {
                // Cut all arcs from this function.
                continue;
            }

            let typing_env = ctx.typing_env(def_id);
            let (thir, expr) = ctx.get_thir(local_id).unwrap();

            // Collect functions called by this function
            let mut visitor = FunctionCalls { def_id, thir: &thir, ctx, calls: IndexSet::new() };
            visitor.visit_expr(&thir[expr]);

            for (called_id, generic_args, call_span) in visitor.calls {
                build_call_graph.function_call(
                    ctx,
                    node,
                    typing_env,
                    called_id,
                    generic_args,
                    call_span,
                );
            }
        }

        Self { graph: build_call_graph.graph }
    }
}

/// Gather the functions calls that appear in a particular function, and store them in `calls`.
struct FunctionCalls<'a, 'tcx> {
    def_id: DefId,
    thir: &'a thir::Thir<'tcx>,
    ctx: &'a TranslationCtx<'tcx>,
    /// Contains:
    /// - The id of the _called_ function.
    /// - The generic args for this call.
    /// - The span of the call (for error messages).
    calls: IndexSet<(DefId, &'tcx GenericArgs<'tcx>, Span)>,
}

impl<'a, 'tcx> Visitor<'a, 'tcx> for FunctionCalls<'a, 'tcx> {
    fn thir(&self) -> &'a thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'a thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Call { fun, fn_span, .. } => {
                if let &FnDef(def_id, generic_args) = self.thir[fun].ty.kind() {
                    self.calls.insert((def_id, generic_args, fn_span));
                }
            }
            thir::ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                // If this is None there must be a type error that will be reported later so we can skip this silently.
                let Some((thir, expr)) = self.ctx.get_thir(closure_id) else { return };
                let mut closure_visitor = FunctionCalls {
                    def_id: self.def_id,
                    thir: &thir,
                    ctx: self.ctx,
                    calls: std::mem::take(&mut self.calls),
                };
                thir::visit::walk_expr(&mut closure_visitor, &thir[expr]);
                self.calls.extend(closure_visitor.calls);
            }
            thir::ExprKind::Loop { .. } => {
                let fun_span = self.ctx.def_span(self.def_id);
                let mut error =
                    self.ctx.error(fun_span, "`#[terminates]` function must not contain loops.");
                error.span_note(expr.span, "looping occurs here");
                error.emit();
            }
            _ => {}
        }
        thir::visit::walk_expr(self, expr);
    }
}

/// Gather the loops in `ghost!` code for a given function.
struct GhostLoops<'thir, 'tcx> {
    thir: &'thir thir::Thir<'tcx>,
    ctx: &'thir TranslationCtx<'tcx>,
    is_in_ghost: bool,
}

impl<'thir, 'tcx> Visitor<'thir, 'tcx> for GhostLoops<'thir, 'tcx> {
    fn thir(&self) -> &'thir thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Closure(box thir::ClosureExpr { closure_id, .. }) => {
                // If this is None there must be a type error that will be reported later so we can skip this silently.
                let Some((thir, expr)) = self.ctx.get_thir(closure_id) else { return };
                let mut closure_visitor =
                    GhostLoops { thir: &thir, ctx: self.ctx, is_in_ghost: self.is_in_ghost };
                thir::visit::walk_expr(&mut closure_visitor, &thir[expr]);
            }
            thir::ExprKind::Loop { .. } if self.is_in_ghost => {
                self.ctx.error(expr.span, "`ghost!` blocks must not contain loops.").emit();
            }
            thir::ExprKind::Scope { lint_level: thir::LintLevel::Explicit(hir_id), .. } => {
                if super::is_ghost_block(self.ctx.tcx, hir_id) {
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
    fn visit_term(&mut self, term: &Term<'tcx>) {
        super_visit_term(term, self);
        if let TermKind::Call { id, subst, args: _ } = &term.kind {
            self.results.insert((*id, subst, term.span));
        }
    }
}
