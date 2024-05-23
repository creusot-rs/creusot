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

use crate::{ctx::TranslationCtx, specification::contract_of, util};
use indexmap::{IndexMap, IndexSet};
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_infer::{
    infer::TyCtxtInferExt,
    traits::{ObligationCause, TraitObligation},
};
use rustc_middle::{
    thir,
    ty::{EarlyBinder, FnDef, GenericArgs, ParamEnv, TyCtxt, TypeVisitableExt},
};
use rustc_span::Span;
use rustc_trait_selection::traits::SelectionContext;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FunctionInstance<'tcx> {
    def_id: DefId,
    generic_args: &'tcx GenericArgs<'tcx>,
}

/// An approximation of the call graph: functions are _not_ monomorphized.
///
/// This is used to detect mutually recursive calls of functions not marked with `#[non_terminating]`.
#[derive(Default, Debug)]
struct CallGraph<'tcx>(IndexMap<FunctionInstance<'tcx>, Function<'tcx>>);

#[derive(Default, Debug)]
struct Function<'tcx> {
    /// `true` if the function has a `#[variant]` annotation.
    ///
    /// For now, mutually recursive functions are never allowed, so this only matter for
    /// the simple recursion check.
    has_variant: bool,
    /// `Some` if the function contains a loop construct (contains the location of the loop).
    ///
    /// The body of external function are not visited, so this field will be `false`.
    has_loops: Option<Span>,
    /// Indices of the functions called by this function.
    ///
    /// Also contains the span of the callsite, for error messages.
    calls: IndexMap<FunctionInstance<'tcx>, Span>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ToVisit<'tcx> {
    /// The function is defined in the crate
    Local { function_def_id: LocalDefId, generic_args: &'tcx GenericArgs<'tcx> },
    /// The function is defined in another crate.
    ///
    /// We keep the generic parameters it was instantiated with, so that trait
    /// parameters can be specialized to specific instances.
    Extern { caller_def_id: DefId, function_def_id: DefId, generic_args: &'tcx GenericArgs<'tcx> },
}
impl<'tcx> ToVisit<'tcx> {
    fn def_id(&self) -> DefId {
        match self {
            ToVisit::Local { function_def_id, .. } => function_def_id.to_def_id(),
            ToVisit::Extern { function_def_id, .. } => *function_def_id,
        }
    }
    fn generic_args(&self) -> &'tcx GenericArgs<'tcx> {
        match self {
            ToVisit::Local { generic_args, .. } | ToVisit::Extern { generic_args, .. } => {
                generic_args
            }
        }
    }
}

/// Validate that a `#[terminates]` function cannot loop indefinitely. This includes:
/// - forbidding program function from using loops of any kind (this should be relaxed
/// later).
/// - forbidding (mutual) recursive calls, especially when traits are involved.
///
/// Note that for logical functions, these are relaxed: we don't check loops, nor simple
/// recursion, because why3 will handle it for us.
pub(crate) fn validate_terminates(ctx: &mut TranslationCtx) {
    ctx.tcx.dcx().abort_if_errors(); // There may have been errors before, if a `#[terminates]` calls a non-`#[terminates]`.
    let mut call_graph = CallGraph::default();

    let mut is_pearlite = IndexSet::<FunctionInstance>::new();
    let mut already_visited = IndexSet::<ToVisit>::new();
    let mut to_visit: Vec<ToVisit> = ctx
        .hir()
        .body_owners()
        .filter_map(|d| {
            if !(util::is_pearlite(ctx.tcx, d.to_def_id())
                || contract_of(ctx, d.to_def_id()).terminates)
            {
                // Only consider functions marked with `terminates`: we already ensured that a `terminates` functions only calls other `terminates` functions.
                None
            } else {
                Some(ToVisit::Local {
                    function_def_id: d,
                    generic_args: GenericArgs::identity_for_item(ctx.tcx, d),
                })
            }
        })
        .collect();

    while let Some(visit) = to_visit.pop() {
        let caller_def_id = visit.def_id();
        if util::is_trusted(ctx.tcx, caller_def_id) {
            let generic_args = visit.generic_args();
            // FIXME: does this work with trait functions marked `#[terminates]`/`#[pure]` ?
            call_graph.0.insert(
                FunctionInstance { def_id: caller_def_id, generic_args },
                Function { has_variant: false, has_loops: None, calls: IndexMap::default() },
            );
        } else {
            match visit {
                // Function defined in the current crate: visit its body
                ToVisit::Local { function_def_id: local_id, generic_args } => {
                    let caller_def_id = local_id.to_def_id();
                    let param_env = ctx.tcx.param_env(caller_def_id);
                    let tcx = ctx.tcx;
                    let (thir, expr) = ctx.thir_body(local_id).unwrap();
                    let thir = thir.borrow();
                    let mut visitor = FunctionCalls {
                        thir: &thir,
                        tcx,
                        generic_args,
                        param_env,
                        calls: IndexSet::new(),
                        has_loops: None,
                    };
                    <FunctionCalls as thir::visit::Visitor>::visit_expr(&mut visitor, &thir[expr]);
                    let (visited_calls, pearlite_func, has_loops) =
                        (visitor.calls, util::is_pearlite(tcx, caller_def_id), visitor.has_loops);

                    let mut calls = IndexMap::new();
                    for (function_def_id, span, subst) in visited_calls {
                        if !ctx.tcx.is_mir_available(function_def_id) {
                            continue;
                        }

                        let next_visit = if let Some(local) = function_def_id.as_local() {
                            ToVisit::Local { function_def_id: local, generic_args: subst }
                        } else {
                            ToVisit::Extern { caller_def_id, function_def_id, generic_args: subst }
                        };
                        if already_visited.insert(next_visit) {
                            to_visit.push(next_visit);
                        }

                        calls.insert(
                            FunctionInstance { def_id: function_def_id, generic_args: subst },
                            span,
                        );
                    }
                    let instance = FunctionInstance { def_id: caller_def_id, generic_args };
                    if pearlite_func {
                        is_pearlite.insert(instance);
                    }
                    call_graph.0.insert(
                        instance,
                        Function {
                            has_variant: util::has_variant_clause(ctx.tcx, caller_def_id),
                            calls,
                            has_loops,
                        },
                    );
                }
                // Function defined in another crate: assume all the functions corresponding to its trait bounds can be called.
                ToVisit::Extern { caller_def_id, function_def_id, generic_args } => {
                    let mut calls = IndexMap::new();
                    for bound in ctx.tcx.param_env(function_def_id).caller_bounds() {
                        let Some(clause) = bound.as_trait_clause() else { continue };

                        // Let's try to find if this specific invocation can be specialized to a known implementation
                        let actual_clause = EarlyBinder::bind(clause.skip_binder())
                            .instantiate(ctx.tcx, generic_args);
                        let param_env = ctx.tcx.param_env(caller_def_id);
                        let obligation = TraitObligation::new(
                            ctx.tcx,
                            ObligationCause::dummy(),
                            param_env,
                            actual_clause,
                        );
                        let infer_ctx = ctx.infer_ctxt().intercrate(true).build();
                        let mut selection_ctx = SelectionContext::new(&infer_ctx);
                        let impl_def_id = if actual_clause.trait_ref.has_param() {
                            // else this crashes the trait selection.
                            None
                        } else {
                            match selection_ctx.select(&obligation) {
                                Ok(Some(source)) => match source {
                                    rustc_infer::traits::ImplSource::UserDefined(source) => {
                                        Some(source.impl_def_id)
                                    }
                                    rustc_infer::traits::ImplSource::Param(_) => {
                                        // FIXME: we take the conservative approach here, but what does this case actually mean ?
                                        None
                                    }
                                    // Used for marker traits (no functions anyway) and trait object/unsized variables (we really don't know what they can call)
                                    rustc_infer::traits::ImplSource::Builtin(_, _) => None,
                                },
                                Ok(None) => None,
                                Err(_) => None,
                            }
                        };

                        if let Some(impl_id) = impl_def_id {
                            // Yes, we can specialize !
                            for &item in ctx.tcx.associated_item_def_ids(impl_id) {
                                let item_kind = ctx.tcx.def_kind(item);
                                if item_kind == DefKind::AssocFn {
                                    let params = GenericArgs::identity_for_item(ctx.tcx, item);
                                    let span = ctx.tcx.def_span(function_def_id);
                                    let instance =
                                        FunctionInstance { def_id: item, generic_args: params };
                                    calls.insert(instance, span);
                                    call_graph.0.entry(instance).or_default().has_variant =
                                        util::has_variant_clause(ctx.tcx, item);
                                    let next_visit = if let Some(local) = item.as_local() {
                                        ToVisit::Local {
                                            function_def_id: local,
                                            generic_args: params, // TODO: are those the right ones ?
                                        }
                                    } else {
                                        ToVisit::Extern {
                                            caller_def_id: function_def_id,
                                            function_def_id: item,
                                            generic_args: params,
                                        }
                                    };
                                    if already_visited.insert(next_visit) {
                                        to_visit.push(next_visit);
                                    }
                                }
                            }
                        } else {
                            // We call the most generic version of the trait functions.
                            // As such, we don't consider this to be an actual call: we cannot resolve it to any concrete function yet.
                        }
                    }
                    let default_params =
                        EarlyBinder::bind(GenericArgs::identity_for_item(ctx.tcx, function_def_id))
                            .instantiate(ctx.tcx, generic_args);
                    call_graph.0.insert(
                        FunctionInstance { def_id: function_def_id, generic_args: default_params },
                        Function { has_variant: true, has_loops: None, calls },
                    );
                }
            }
        }
    }

    for f in call_graph.0.keys().copied().collect::<Vec<_>>() {
        let def_id = f.def_id;
        // are we part of a `impl` block ?
        let Some(impl_id) = ctx.impl_of_method(def_id) else {
            continue;
        };
        // Maps every item in the impl block to the item defined in the trait
        let map = ctx.impl_item_implementor_ids(impl_id);
        let item_id = std::cell::Cell::new(def_id);
        // Find the corresponding trait
        // Can't iterate directly on this structure, so we have to do this :(
        map.items().all(|(trait_id, impl_id)| {
            if *impl_id == def_id {
                item_id.set(*trait_id);
                return false;
            }
            true
        });
        let item_id = item_id.get();
        if item_id == def_id {
            // This is just an inherent impl, not a trait
            continue;
        }
    }

    // Detect simple recursion, and loops
    for (fun_inst, calls) in &mut call_graph.0 {
        if is_pearlite.contains(fun_inst) {
            // No need for this: pearlite fonctions always generate a proof obligation for termination.
            calls.calls.remove(fun_inst);
            continue;
        }
        if let Some(&call_span) = calls.calls.get(fun_inst) {
            calls.calls.remove(fun_inst);
            if !calls.has_variant && fun_inst.def_id.is_local() {
                let fun_span = ctx.tcx.def_span(fun_inst.def_id);
                let mut error =
                    ctx.error(fun_span, "Recursive function without a `#[variant]` clause");
                error.span_note(call_span, "Recursive call happens here");
                error.emit();
            }
        }
        if let Some(loop_span) = calls.has_loops {
            let fun_span = ctx.tcx.def_span(fun_inst.def_id);
            let mut error = ctx.error(fun_span, "`#[terminates]` function must not contain loops.");
            error.span_note(loop_span, "looping occurs here");
            error.emit();
        }
    }

    // detect mutual recursion
    let cycles = find_cycles(&call_graph);
    for mut cycle in cycles {
        if cycle.iter().all(|inst| !inst.def_id.is_local()) {
            // The cycle needs to involve at least one function in the current crate.
            continue;
        }
        let root = cycle.pop().unwrap();
        let mut next_instance = root;
        let mut error = ctx.error(
            ctx.def_span(root.def_id),
            &format!(
                "Mutually recursive functions: when calling `{}`...",
                ctx.tcx.def_path_str(root.def_id)
            ),
        );
        let mut instance;
        while let Some(id) = cycle.pop() {
            instance = next_instance;
            next_instance = id;
            let span = call_graph.0[&instance].calls[&next_instance];
            error.span_note(
                span,
                format!(
                    "then `{}` calls `{}`...",
                    ctx.tcx.def_path_str(instance.def_id),
                    ctx.tcx.def_path_str(next_instance.def_id)
                ),
            );
        }
        instance = next_instance;
        next_instance = root;
        let span = call_graph.0[&instance].calls[&next_instance];
        error.span_note(
            span,
            format!(
                "finally `{}` calls `{}`.",
                ctx.tcx.def_path_str(instance.def_id),
                ctx.tcx.def_path_str(next_instance.def_id)
            ),
        );
        error.emit();
    }

    ctx.tcx.dcx().abort_if_errors();
}

/// Gather the functions calls that appear in a particular function.
struct FunctionCalls<'thir, 'tcx> {
    thir: &'thir thir::Thir<'tcx>,
    tcx: TyCtxt<'tcx>,
    /// Generic arguments that the function was intantiated with.
    generic_args: &'tcx GenericArgs<'tcx>,
    param_env: ParamEnv<'tcx>,
    /// Contains:
    /// - The id of the _called_ function
    /// - The span of the call (for error messages)
    /// - The generic arguments instantiating the call
    calls: IndexSet<(DefId, Span, &'tcx GenericArgs<'tcx>)>,
    /// `true` if the function contains a loop construct.
    has_loops: Option<Span>,
}

impl<'thir, 'tcx> thir::visit::Visitor<'thir, 'tcx> for FunctionCalls<'thir, 'tcx> {
    fn thir(&self) -> &'thir thir::Thir<'tcx> {
        self.thir
    }

    fn visit_expr(&mut self, expr: &'thir thir::Expr<'tcx>) {
        match expr.kind {
            thir::ExprKind::Call { fun, fn_span, .. } => {
                if let &FnDef(def_id, subst) = self.thir[fun].ty.kind() {
                    let subst = EarlyBinder::bind(self.tcx.erase_regions(subst))
                        .instantiate(self.tcx, self.generic_args);
                    let (def_id, args) =
                        match self.tcx.resolve_instance(self.param_env.and((def_id, subst))) {
                            Ok(Some(instance)) => (instance.def.def_id(), instance.args),
                            _ => (def_id, subst),
                        };
                    self.calls.insert((def_id, fn_span, args));
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
                    generic_args: GenericArgs::identity_for_item(self.tcx, closure_id.to_def_id()),
                    param_env: self.param_env,
                    calls: std::mem::take(&mut self.calls),
                    has_loops: None,
                };
                thir::visit::walk_expr(&mut closure_visitor, &thir[expr]);
                self.calls = closure_visitor.calls;
            }
            thir::ExprKind::Loop { .. } => self.has_loops = Some(expr.span),
            _ => {}
        }
        thir::visit::walk_expr(self, expr);
    }
}

/// Finds all the cycles in the call graph.
fn find_cycles<'tcx>(graph: &CallGraph<'tcx>) -> IndexSet<Vec<FunctionInstance<'tcx>>> {
    let mut find_cycles = FindCycles {
        graph,
        stack: Vec::new(),
        visited: IndexSet::new(),
        ordering: IndexMap::new(),
        detected_cycles: IndexSet::new(),
    };
    for &v in graph.0.keys() {
        let idx = find_cycles.ordering.len();
        find_cycles.ordering.entry(v).or_insert(idx);
        if find_cycles.visited.insert(v) {
            find_cycles.stack = vec![v];
            find_cycles.process_dfs_tree();
        }
    }
    find_cycles.detected_cycles
}

struct FindCycles<'graph, 'tcx> {
    /// The call graph of functions. We will try to find cycles in that graph.
    graph: &'graph CallGraph<'tcx>,
    /// The current path of called function, e.g. `stack[i]` calls `stack[i + 1]`.
    ///
    /// All nodes in the stack must also be in `visited`.
    stack: Vec<FunctionInstance<'tcx>>,
    /// Nodes in the `graph` that were already visited.
    visited: IndexSet<FunctionInstance<'tcx>>,
    /// Contains an index to order `FunctionInstance`s. Used to avoid flagging the same
    ///  cycle twice in different orders.
    ordering: IndexMap<FunctionInstance<'tcx>, usize>,
    /// The resulting set of cycles found.
    detected_cycles: IndexSet<Vec<FunctionInstance<'tcx>>>,
}

impl<'tcx> FindCycles<'_, 'tcx> {
    /// Process the call graph depth-first in order to find cycles.
    fn process_dfs_tree(&mut self) {
        let top = *self.stack.last().unwrap();
        let top_calls = &self.graph.0[&top];
        for &v in top_calls.calls.keys() {
            let idx = self.ordering.len();
            self.ordering.entry(v).or_insert(idx);
            if self.visited.insert(v) {
                self.stack.push(v);
                self.process_dfs_tree();
            } else {
                self.collect_cycle(v);
            }
        }
        self.visited.remove(&top);
        self.stack.pop();
    }

    fn collect_cycle(&mut self, v: FunctionInstance<'tcx>) {
        let mut cycle = vec![self.stack.pop().unwrap()];
        while let Some(v2) = self.stack.pop() {
            cycle.push(v2);
            if v2 == v {
                self.stack.push(v);
                break;
            }
        }

        // Order the cycle, to avoid detecting the same cycle starting at different positions
        let (min_idx, _) = cycle
            .iter()
            .enumerate()
            .min_by(|(_, def1), (_, def2)| self.ordering[*def1].cmp(&self.ordering[*def2]))
            .unwrap();
        let mut result = Vec::new();
        let mut idx = (min_idx + 1) % cycle.len();
        while idx != min_idx {
            result.push(cycle[idx]);
            idx = (idx + 1) % cycle.len();
        }
        result.push(cycle[idx]);

        self.detected_cycles.insert(result);
    }
}
