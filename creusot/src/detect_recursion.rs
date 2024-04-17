//! Detection of mutually recursive functions.
//!
//! Care is taken around the interaction with traits, like the following example:
//! ```
//! pub trait Foo {
//!     fn foo() {}
//! }
//!
//! impl Foo for i32 {
//!     fn foo() {
//!         bar::<i32>();
//!     }
//! }
//!
//! // `bar` is recursive if `T` is `i32`
//! pub fn bar<T: Foo>() {
//!     T::foo();
//! }
//! ```

use crate::ctx::TranslationCtx;
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
    mir::{visit::Visitor, Location, Terminator, TerminatorKind},
    ty::{EarlyBinder, GenericArgs, ParamEnv, TyCtxt},
};
use rustc_span::Span;
use rustc_trait_selection::traits::SelectionContext;

type FunctionInstance<'tcx> = (DefId, &'tcx GenericArgs<'tcx>);

/// An approximation of the call graph: functions are _not_ monomorphized.
///
/// This is used to detect mutually recursive calls of functions not marked with `#[non_terminating]`.
#[derive(Default, Debug)]
struct CallGraph<'tcx>(IndexMap<FunctionInstance<'tcx>, Function<'tcx>>);

#[derive(Default, Debug)]
struct Function<'tcx> {
    /// `true` if the function is allowed to be recursive, i.e. it has a `#[variant]` annotation.
    ///
    /// For now, mutually recursive functions are never allowed.
    can_be_recursive: bool,
    /// Indices of the functions called by this function.
    ///
    /// Also contains the span of the callsite, for error messages.
    calls: IndexMap<FunctionInstance<'tcx>, Span>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum ToVisit<'tcx> {
    /// The function is defined in the crate
    Local { function_def_id: LocalDefId, generic_params: &'tcx GenericArgs<'tcx> },
    /// The function is defined in another crate.
    ///
    /// We keep the generic parameters it was instantiated with, so that trait
    /// parameters can be specialized to specific instances.
    Extern { caller_def_id: DefId, function_def_id: DefId, generic_params: &'tcx GenericArgs<'tcx> },
}
impl<'tcx> ToVisit<'tcx> {
    fn def_id(&self) -> DefId {
        match self {
            ToVisit::Local { function_def_id, .. } => function_def_id.to_def_id(),
            ToVisit::Extern { function_def_id, .. } => *function_def_id,
        }
    }
}
type VisitDefId<'tcx> = IndexSet<ToVisit<'tcx>>;

pub(crate) fn detect_recursion(ctx: &mut TranslationCtx) {
    let mut call_graph = CallGraph::default();
    let mut to_visit: VisitDefId = ctx
        .hir()
        .body_owners()
        .map(|d| ToVisit::Local {
            function_def_id: d,
            generic_params: GenericArgs::identity_for_item(ctx.tcx, d),
        })
        .collect();
    while let Some(&visited) = to_visit.iter().next() {
        if crate::util::is_trusted(ctx.tcx, visited.def_id()) {
            let def_id = visited.def_id();
            // FIXME: does this work with trait functions marked `#[trusted]` ?
            call_graph.0.insert(
                (def_id, GenericArgs::identity_for_item(ctx.tcx, def_id)),
                Function { can_be_recursive: false, calls: IndexMap::default() },
            );
        } else {
            match visited {
                // Function defined in the current crate: visit its body
                ToVisit::Local { function_def_id: local_id, generic_params } => {
                    let def_id = local_id.to_def_id();
                    let body = ctx.body_with_facts(local_id).body.clone();
                    let param_env = ctx.tcx.param_env(def_id);
                    let mut visitor = FunctionCalls {
                        tcx: ctx.tcx,
                        generic_params,
                        param_env,
                        calls: IndexSet::new(),
                    };
                    visitor.visit_body(&body);
                    let mut calls = IndexMap::new();
                    for &(function_def_id, span, subst) in &visitor.calls {
                        if !call_graph.0.contains_key(&(function_def_id, subst)) {
                            if let Some(local) = function_def_id.as_local() {
                                to_visit.insert(ToVisit::Local {
                                    function_def_id: local,
                                    generic_params: subst,
                                });
                            } else {
                                to_visit.insert(ToVisit::Extern {
                                    caller_def_id: def_id,
                                    function_def_id,
                                    generic_params: subst,
                                });
                            }
                        }
                        calls.insert((function_def_id, subst), span);
                    }
                    call_graph.0.insert(
                        (def_id, generic_params),
                        Function {
                            can_be_recursive: crate::util::has_variant_clause(ctx.tcx, def_id),
                            calls: visitor
                                .calls
                                .into_iter()
                                .map(|(d, span, args)| ((d, args), span))
                                .collect(),
                        },
                    );
                }
                // Function defined in another crate: assume all the functions corresponding to its trait bounds can be called.
                ToVisit::Extern { caller_def_id, function_def_id, generic_params } => {
                    let mut calls = IndexMap::new();
                    for bound in ctx.tcx.param_env(function_def_id).caller_bounds() {
                        let Some(clause) = bound.as_trait_clause() else { continue };

                        // Let's try to find if this specific invocation can be specialized to a known implementation
                        let actual_clause = EarlyBinder::bind(clause.skip_binder())
                            .instantiate(ctx.tcx, generic_params);
                        let obligation = TraitObligation::new(
                            ctx.tcx,
                            ObligationCause::dummy(),
                            ctx.tcx.param_env(caller_def_id),
                            actual_clause,
                        );
                        let infer_ctx = ctx.infer_ctxt().intercrate(false).build();
                        let mut selection_ctx = SelectionContext::new(&infer_ctx);
                        let impl_def_id = match selection_ctx.select(&obligation) {
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
                            Err(e) => panic!("{e:?}"),
                        };

                        if let Some(impl_id) = impl_def_id {
                            // Yes, we can specialize !
                            for &item in ctx.tcx.associated_item_def_ids(impl_id) {
                                let item_kind = ctx.tcx.def_kind(item);
                                if item_kind == DefKind::AssocFn {
                                    let params = EarlyBinder::bind(GenericArgs::identity_for_item(
                                        ctx.tcx, item,
                                    ))
                                    .instantiate(ctx.tcx, generic_params);
                                    calls.insert((item, params), ctx.tcx.def_span(function_def_id));
                                    call_graph
                                        .0
                                        .entry((item, params))
                                        .or_default()
                                        .can_be_recursive =
                                        crate::util::has_variant_clause(ctx.tcx, item);
                                    let visit = if let Some(local) = item.as_local() {
                                        ToVisit::Local {
                                            function_def_id: local,
                                            generic_params: params, // TODO: are those the right ones ?
                                        }
                                    } else {
                                        ToVisit::Extern {
                                            caller_def_id: function_def_id,
                                            function_def_id: item,
                                            generic_params: params,
                                        }
                                    };
                                    to_visit.insert(visit);
                                }
                            }
                        } else {
                            // We call the most generic version of the trait functions.
                            // As such, we don't consider this to be an actual call: we cannot resolve it to any concrete function yet.
                        }
                    }
                    let default_params =
                        EarlyBinder::bind(GenericArgs::identity_for_item(ctx.tcx, function_def_id))
                            .instantiate(ctx.tcx, generic_params);
                    call_graph.0.insert(
                        (function_def_id, default_params),
                        Function {
                            can_be_recursive: true, // External functions can always be simply recursive
                            calls,
                        },
                    );
                }
            }
        }
        to_visit.remove(&visited);
    }
    for (def_id, _) in call_graph.0.keys().copied().collect::<Vec<_>>() {
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

    // Detect simple recursion
    for (fun_id, calls) in &mut call_graph.0 {
        if let Some(&call_span) = calls.calls.get(fun_id) {
            calls.calls.remove(fun_id);
            if !calls.can_be_recursive && fun_id.0.is_local() {
                let fun_span = ctx.tcx.def_span(fun_id.0);
                let mut error =
                    ctx.error(fun_span, "Recursive function without a `#[variant]` clause");
                error.span_note(call_span, "Recursive call happens here");
                error.emit();
            }
        }
    }

    // detect mutual recursion
    let cycles = find_cycles(&call_graph);
    for mut cycle in cycles {
        if cycle.iter().all(|id| !id.0.is_local()) {
            // The cycle needs to involve at least one function in the current crate.
            continue;
        }
        let root_id = cycle.pop().unwrap();
        let mut next_def_id = root_id;
        let mut error = ctx.error(
            ctx.def_span(root_id.0),
            &format!(
                "Mutually recursive functions: when calling {}...",
                ctx.tcx.def_path_str(root_id.0)
            ),
        );
        let mut def_id;
        while let Some(id) = cycle.pop() {
            def_id = next_def_id;
            next_def_id = id;
            let span = call_graph.0[&def_id].calls[&next_def_id];
            error.span_note(
                span,
                format!(
                    "then {} calls {}...",
                    ctx.tcx.def_path_str(def_id.0),
                    ctx.tcx.def_path_str(next_def_id.0)
                ),
            );
        }
        def_id = next_def_id;
        next_def_id = root_id;
        let span = call_graph.0[&def_id].calls[&next_def_id];
        error.span_note(
            span,
            format!(
                "finally {} calls {}.",
                ctx.tcx.def_path_str(def_id.0),
                ctx.tcx.def_path_str(next_def_id.0)
            ),
        );
        error.emit();
    }

    ctx.tcx.dcx().abort_if_errors();

    // FIXME:
    // - mark which functions are "terminating" or "ghost"
    // - This will eventually need a proof: see TESTING/recursion_proof.typ.
}

/// Gather the functions calls that appear in a particular function.
struct FunctionCalls<'tcx> {
    tcx: TyCtxt<'tcx>,
    generic_params: &'tcx GenericArgs<'tcx>,
    param_env: ParamEnv<'tcx>,
    /// Contains:
    /// - The id of the called function
    /// - The span of the call (for error messages)
    /// - The generic arguments instantiating the call
    calls: IndexSet<(DefId, Span, &'tcx GenericArgs<'tcx>)>,
}

impl<'tcx> Visitor<'tcx> for FunctionCalls<'tcx> {
    fn super_terminator(&mut self, terminator: &Terminator<'tcx>, _: Location) {
        use ::{
            rustc_middle::mir::{Const, Operand},
            rustc_type_ir::TyKind,
        };

        let Terminator { source_info, kind } = terminator;
        self.visit_source_info(source_info);
        match kind {
            TerminatorKind::Call { func, fn_span, .. } => match func {
                Operand::Copy(_) | Operand::Move(_) => {
                    panic!("No dynamic calls in creusot. Make a proper error instead of a panic.")
                }
                Operand::Constant(op) => match &op.const_ {
                    Const::Val(_, ty) => match ty.kind() {
                        TyKind::FnDef(def_id, subst) | TyKind::Closure(def_id, subst) => {
                            let subst = EarlyBinder::bind(*subst)
                                .instantiate(self.tcx, self.generic_params);
                            let (def_id, args) = match self
                                .tcx
                                .resolve_instance(self.param_env.and((*def_id, subst)))
                            {
                                Ok(Some(instance)) => (instance.def.def_id(), instance.args),
                                _ => (*def_id, subst),
                            };
                            self.calls.insert((def_id, *fn_span, args));
                        }
                        TyKind::FnPtr(_) => panic!("no dynamic calls allowed"),
                        _ => {}
                    },
                    _ => {}
                },
            },
            _ => {}
        }
    }
}

/// Finds all the cycles in the call graph.
fn find_cycles<'tcx>(graph: &CallGraph<'tcx>) -> IndexSet<Vec<FunctionInstance<'tcx>>> {
    let mut visited: IndexSet<FunctionInstance> = IndexSet::new();
    let mut detected_cycles = IndexSet::new();
    for &v in graph.0.keys() {
        if visited.insert(v) {
            let mut stack = vec![v];
            process_dfs_tree(graph, &mut stack, &mut visited, &mut detected_cycles);
        }
    }
    detected_cycles
}

// INPUT
//   Graph = a graph
//   Stack = current path
//   visited = a visited set
//   detectedCycles = a collection of already processed cycles
// OUTPUT
//   Print all cycles in the current DFS Tree
fn process_dfs_tree<'tcx>(
    graph: &CallGraph<'tcx>,
    stack: &mut Vec<FunctionInstance<'tcx>>,
    visited: &mut IndexSet<FunctionInstance<'tcx>>,
    detected_cycles: &mut IndexSet<Vec<FunctionInstance<'tcx>>>,
) {
    let top = *stack.last().unwrap();
    let top_calls = &graph.0[&top];
    for &v in top_calls.calls.keys() {
        if visited.insert(v) {
            stack.push(v);
            process_dfs_tree(graph, stack, visited, detected_cycles);
        } else {
            collect_cycle(stack, v, detected_cycles);
        }
    }
    visited.remove(&top);
    stack.pop();
}

fn collect_cycle<'tcx>(
    stack: &mut Vec<FunctionInstance<'tcx>>,
    v: FunctionInstance<'tcx>,
    detected_cycles: &mut IndexSet<Vec<FunctionInstance<'tcx>>>,
) {
    let mut cycle = vec![stack.pop().unwrap()];
    while let Some(v2) = stack.pop() {
        cycle.push(v2);
        if v2 == v {
            stack.push(v);
            break;
        }
    }

    // Order the cycle, to avoid detecting the same cycle starting at different positions
    let (min_idx, _) =
        cycle.iter().enumerate().min_by(|(_, def1), (_, def2)| def1.cmp(def2)).unwrap();
    let mut result = Vec::new();
    let mut idx = (min_idx + 1) % cycle.len();
    while idx != min_idx {
        result.push(cycle[idx]);
        idx = (idx + 1) % cycle.len();
    }
    result.push(cycle[idx]);

    detected_cycles.insert(result);
}
