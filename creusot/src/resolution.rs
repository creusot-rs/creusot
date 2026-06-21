//! Trait resolution logic
use crate::contracts_items::is_sealed;
use rustc_hir::def_id::DefId;
use rustc_infer::{
    infer::{DefineOpaqueTypes, InferCtxt, TyCtxtInferExt},
    traits::{CodegenObligationError, ObligationCause, specialization_graph::Graph},
};
use rustc_middle::ty::{
    self, Const, ConstKind, GenericArgsRef, ParamConst, ParamEnv, ParamEnvAnd, ParamTy, TraitRef,
    Ty, TyCtxt, TyKind, TypeFoldable, TypeFolder, TypingEnv, TypingMode, Unnormalized,
};
use rustc_span::{DUMMY_SP, ErrorGuaranteed};
use rustc_trait_selection::traits::{ImplSource, InCrate, orphan_check_trait_ref};
use rustc_type_ir::{
    TypeSuperFoldable,
    fast_reject::{TreatParams, simplify_type},
    inherent::Ty as _,
};
use std::{collections::HashMap, iter};

pub enum ImplSelection<'tcx> {
    Found(&'tcx ImplSource<'tcx, ()>),
    UnknownFound,
    None,
}

pub fn select_trait_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    trait_ref: TraitRef<'tcx>,
) -> ImplSelection<'tcx> {
    use ImplSelection::*;
    let source = tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref));
    match source {
        // FIXME: if there are several instances available, `codegen_select_candidate`
        // returns an error, while we would like it to return any of the instances.
        // We need to find another entry point of the trait solver.
        // In the meantime, pretend that we have an instance that we do not know
        Err(CodegenObligationError::Ambiguity) => return UnknownFound,
        Err(_) => return None,
        Ok(source) => Found(source),
    }
}

/// Does Creusot synthesize a structural specification for this unmodeled
/// compiler-builtin call, so its result is NOT left unconstrained?
///
/// Currently this is tuple `Clone`: the trait-level `Clone` contract is empty,
/// so the opaque val carries no law; the backend instead synthesizes the
/// element-wise postcondition, recursing through nested tuples to leaf types
/// (see `elaborator::structural_clone_post`). When this holds, the
/// `opaque_builtin_impl` lint is suppressed.
///
/// CAVEAT: suppression is per-tuple, but a leaf whose own `Clone` is itself
/// unmodeled (a closure, or a user type with a contractless `Clone`) still
/// contributes a vacuous conjunct — so for e.g. `(bool, closure)` the law
/// constrains the modeled fields but leaves that one leaf unconstrained, a
/// (now confined, but still silent) precision loss. The common case — tuples of
/// modeled types at any depth — is fully constrained.
///
/// Only tuple `Clone` and closure `Clone` reach the builtin path. Tuple
/// `PartialEq`/`Ord`/`Hash` and array `Clone` all resolve via real `core` impls
/// (`ImplSource::UserDefined`) — they never reach this arm, so they neither ICE
/// nor get a synthesized law here (tuple `==`/`<` already carry a `deep_model`
/// law from their trait contract; tuple `Hash` is a contractless extern call).
pub(crate) fn synthesizes_builtin_law<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> bool {
    // The `clone_fn` check short-circuits before `subst.type_at(0)`, which would
    // panic for items called with an empty substitution.
    tcx.lang_items().clone_fn() == Some(def_id)
        && matches!(subst.type_at(0).kind(), TyKind::Tuple(tys) if !tys.is_empty())
}

fn select_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    trait_ref: TraitRef<'tcx>,
    trait_item_def_id: DefId,
    substs: GenericArgsRef<'tcx>,
    source: &'tcx ImplSource<'tcx, ()>,
) -> TraitResolved<'tcx> {
    match source {
        ImplSource::UserDefined(impl_data) => {
            // Find the id of the actual associated method we will be running
            let leaf_def = tcx
                .trait_def(trait_ref.def_id)
                .ancestors(tcx, impl_data.impl_def_id)
                .unwrap()
                .leaf_def(tcx, trait_item_def_id)
                .unwrap_or_else(|| {
                    panic!("{:?} not found in {:?}", trait_item_def_id, impl_data.impl_def_id);
                });

            if !(leaf_def.is_final() || is_sealed(tcx, leaf_def.item.def_id)) {
                // The instance we found is not final nor sealed. There might be a speciallized
                // matching instance.
                // We have found a user-defined instance, so we know for sure that there is no
                // matching instance in a future crate. Hence we explore the descendents of the
                // current node to make sure that there is no specialized matching instances.

                let Ok(gt) = GraphTraversal::new(tcx, typing_env.param_env, trait_ref) else {
                    // Cannot find graph because of an error. Return a dummy value.
                    return TraitResolved::UnknownFound;
                };

                let r = gt.traverse_descendants(impl_data.impl_def_id, |node| {
                    if tcx.impl_item_implementor_ids(node).get(&trait_item_def_id).is_some() {
                        // This is a matching instance
                        GraphTraversalAction::Interrupt
                    } else if tcx.defaultness(node).is_final() {
                        // This is a final instance without a matching implementation
                        // We know that a specializing impl cannot have an implementation
                        // for our method
                        GraphTraversalAction::Skip
                    } else {
                        GraphTraversalAction::Traverse
                    }
                });
                if !r {
                    return TraitResolved::UnknownFound;
                }
            }

            // Translate the original substitution into one on the selected impl method
            let infcx = tcx.infer_ctxt().build(TypingMode::non_body_analysis());
            let args = rustc_trait_selection::traits::translate_args(
                &infcx,
                typing_env.param_env,
                impl_data.impl_def_id,
                impl_data.args,
                leaf_def.defining_node,
            );
            let substs = substs.rebase_onto(tcx, trait_ref.def_id, args);

            let leaf_substs = tcx.erase_and_anonymize_regions(substs);

            TraitResolved::Instance {
                def: (leaf_def.item.def_id, leaf_substs),
                impl_: ImplSource_::Impl(impl_data.impl_def_id, impl_data.args),
            }
        }
        ImplSource::Param(_) => {
            // Check whether the default impl from the trait def is sealed
            if is_sealed(tcx, trait_item_def_id) {
                return TraitResolved::Instance {
                    def: (trait_item_def_id, substs),
                    impl_: ImplSource_::Param,
                };
            }

            // TODO: we could try to explore the graph to determine if we can be sure
            // that another impl is guaranteed to be the one we are seaching for

            TraitResolved::UnknownFound
        }
        ImplSource::Builtin(_, _) => {
            if matches!(substs.type_at(0).kind(), rustc_middle::ty::Dynamic(_, _)) {
                // These types are not supported, but we want to display a proper error message because
                // they are rather common in real Rust code, and this is not the right place to emit
                // such an error message.
                return TraitResolved::UnknownFound;
            }

            if [
                tcx.lang_items().fn_trait(),
                tcx.lang_items().fn_mut_trait(),
                tcx.lang_items().fn_once_trait(),
            ]
            .contains(&Some(trait_ref.def_id))
            {
                match *substs.type_at(0).kind() {
                    TyKind::Closure(closure_def_id, closure_substs) => {
                        return TraitResolved::Instance {
                            def: (closure_def_id, closure_substs),
                            impl_: ImplSource_::Fn,
                        };
                    }
                    TyKind::FnDef(did, subst) => {
                        return TraitResolved::Instance {
                            def: (did, subst),
                            impl_: ImplSource_::Fn,
                        };
                    }
                    _ => (),
                }
            }

            // Builtin trait impls we don't model specifically — the
            // compiler-synthesized impls reaching here are tuple `Clone` and
            // closure `Clone` (tuple `PartialEq`/`Ord`/`Hash` and array `Clone`
            // have real `core` impls and resolve via `UserDefined` instead). Rather
            // than ICE-ing, treat them as an unknown-but-present instance (opaque),
            // mirroring the `Dynamic` case above. This is sound: an opaque
            // resolution loses precision (the call is treated abstractly) but never
            // correctness. `UnknownBuiltin` behaves exactly like `UnknownFound`
            // downstream, but lets the caller pinpoint that the opacity comes from
            // an unmodeled builtin impl (used to emit the `opaque_builtin_impl`
            // lint, so the precision loss is not silent).
            TraitResolved::UnknownBuiltin
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub(crate) enum ImplSource_<'tcx> {
    /// The id and substitution of the impl block, if any.
    Impl(DefId, GenericArgsRef<'tcx>),
    Param,
    Fn,
}

/// The result of [`Self::resolve_assoc_item_opt`]: given the id of a trait item and some
/// type parameters, we might find an actual implementation of the item.
#[derive(Debug, Clone)]
pub(crate) enum TraitResolved<'tcx> {
    NotATraitItem,
    /// An instance (like `impl Clone for i32 { ... }`) exists for the given type parameters.
    Instance {
        /// The id and substitution of the specific item found (e.g. the `clone` function in `impl Clone for i32`).
        def: (DefId, GenericArgsRef<'tcx>),
        impl_: ImplSource_<'tcx>,
    },
    /// A known instance exists, but we don't know which one.
    UnknownFound,
    /// A known instance exists but is an unmodeled compiler-builtin impl (tuple
    /// `Clone` or closure `Clone`). Kept as a distinct variant only so the
    /// translation can emit the `opaque_builtin_impl` lint at the call site (and
    /// synthesize a law for tuple `Clone`, see `synthesizes_builtin_law`).
    ///
    /// Only arises when resolving a *program* function call (`Clone::clone` on a
    /// tuple/closure). It is therefore unreachable when resolving logic functions,
    /// constants, or the `Resolve`/`Invariant` traits (none of which have builtin
    /// impls) — those sites treat it as `unreachable!()`. Where it is reachable, it
    /// is treated like [`Self::UnknownFound`] (opaque, sound) except at the lint
    /// emission in `terminator.rs`, the one site that discriminates the two.
    UnknownBuiltin,
    /// No instance exists, we return extra data to query whether an instance might exist
    /// (via specialization or potentially defined in another crate).
    ///
    /// For example, in `fn<T> f(x: T) { let _ = x.clone() }`, we  don't have an
    /// instance for `T::clone` until we know more about `T`.
    NoInstance(NoInstance<'tcx>),
}

impl<'tcx> TraitResolved<'tcx> {
    /// Try to resolve a trait item to the item in an `impl` block, given some typing context.
    ///
    /// # Parameters
    /// - `tcx`: The global context
    /// - `typing_env`: The scope of type variables, see <https://rustc-dev-guide.rust-lang.org/param_env/param_env_summary.html>.
    /// - `trait_item_def_id`: The trait item we are trying to resolve.
    /// - `substs`: The type parameters we are instantiating the trait item with. This
    ///   can include the `Self` parameter.
    pub(crate) fn resolve_item(
        tcx: TyCtxt<'tcx>,
        typing_env: TypingEnv<'tcx>,
        trait_item_def_id: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> Self {
        trace!("TraitResolved::resolve {:?} {:?}", trait_item_def_id, substs);

        let trait_ref = if let Some(did) = tcx.trait_of_assoc(trait_item_def_id) {
            TraitRef::from_assoc(tcx, did, substs)
        } else {
            return TraitResolved::NotATraitItem;
        };
        let trait_ref = tcx.normalize_erasing_regions(typing_env, Unnormalized::new(trait_ref));

        let source = match select_trait_impl(tcx, typing_env, trait_ref) {
            ImplSelection::Found(source) => source,
            ImplSelection::UnknownFound => return Self::UnknownFound,
            ImplSelection::None => {
                return Self::NoInstance(NoInstance { tcx, typing_env, trait_ref });
            }
        };
        trace!("TraitResolved::resolve {source:?}",);
        select_method(tcx, typing_env, trait_ref, trait_item_def_id, substs, source)
    }

    pub(crate) fn to_opt(
        self,
        did: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            TraitResolved::Instance { def, impl_: _ } => Some(def),
            TraitResolved::NotATraitItem
            | TraitResolved::UnknownFound
            | TraitResolved::UnknownBuiltin => Some((did, substs)),
            _ => None,
        }
    }
}

fn instantiate_params_with_infer<'tcx, T: TypeFoldable<TyCtxt<'tcx>>>(
    ctx: &InferCtxt<'tcx>,
    value: T,
) -> T {
    struct Folder<'a, 'tcx> {
        ctx: &'a InferCtxt<'tcx>,
        tys: HashMap<ParamTy, Ty<'tcx>>,
        consts: HashMap<ParamConst, Const<'tcx>>,
    }
    impl<'tcx> TypeFolder<TyCtxt<'tcx>> for Folder<'_, 'tcx> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.ctx.tcx
        }

        fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
            match *t.kind() {
                TyKind::Param(param) => {
                    *self.tys.entry(param).or_insert_with(|| self.ctx.next_ty_var(DUMMY_SP))
                }
                _ => t.super_fold_with(self),
            }
        }

        fn fold_const(&mut self, c: Const<'tcx>) -> Const<'tcx> {
            match c.kind() {
                ConstKind::Param(param) => {
                    *self.consts.entry(param).or_insert_with(|| self.ctx.next_const_var(DUMMY_SP))
                }
                _ => c.super_fold_with(self),
            }
        }
    }
    value.fold_with(&mut Folder { ctx, tys: Default::default(), consts: Default::default() })
}

/// Data for further examination when resolution returns `TraitResolved::NoInstance`
/// This is used by `crate::backend::resolve` and `crate::backend::ty_inv`.
#[derive(Clone)]
pub struct NoInstance<'tcx> {
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    trait_ref: TraitRef<'tcx>,
}

impl std::fmt::Debug for NoInstance<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("NoInstance").field("trait_ref", &self.trait_ref).finish_non_exhaustive()
    }
}

impl NoInstance<'_> {
    pub fn trait_ref_is_specializable(&self) -> bool {
        let Ok(gt) = GraphTraversal::new(self.tcx, self.typing_env.param_env, self.trait_ref)
        else {
            return false;
        };

        if gt.remote_crates_allow_impls() {
            // A downstream or cousin crate is allowed to implement some
            // generic parameters of this trait-ref.
            return false;
        }

        // Check whether one of the descendents of start_node applies too
        !gt.traverse_descendants(self.trait_ref.def_id, |node| {
            if self.tcx.defaultness(node).is_default() {
                GraphTraversalAction::Traverse
            } else {
                // This final instance may match our trait_ref
                GraphTraversalAction::Interrupt
            }
        })
    }
}

// Type used for traversing the specialization graph in order to find ambiguous instances
struct GraphTraversal<'tcx> {
    tcx: TyCtxt<'tcx>,
    infcx: InferCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    trait_ref: TraitRef<'tcx>,
    graph: &'tcx Graph,
}

enum GraphTraversalAction {
    Skip,
    Traverse,
    Interrupt,
}

impl<'tcx> GraphTraversal<'tcx> {
    fn new(
        tcx: TyCtxt<'tcx>,
        param_env: ParamEnv<'tcx>,
        trait_ref: TraitRef<'tcx>,
    ) -> Result<Self, ErrorGuaranteed> {
        let infcx = tcx.infer_ctxt().ignoring_regions().build(rustc_type_ir::TypingMode::Coherence);
        let ParamEnvAnd { param_env, value: trait_ref } =
            instantiate_params_with_infer(&infcx, param_env.and(trait_ref));

        let graph = tcx.specialization_graph_of(trait_ref.def_id)?;
        Ok(GraphTraversal { tcx, infcx, param_env, trait_ref, graph })
    }

    fn matching_children(&self, node: DefId) -> Box<dyn Iterator<Item = DefId> + '_> {
        let Some(children) = self.graph.children.get(&node) else { return Box::new(iter::empty()) };
        let nonblanket: Box<dyn Iterator<Item = &'tcx DefId>> = if let Some(st) =
            simplify_type(self.tcx, self.trait_ref.self_ty(), TreatParams::InstantiateWithInfer)
        {
            if let Some(v) = children.non_blanket_impls.get(&st) {
                Box::new(v.iter())
            } else {
                Box::new(iter::empty())
            }
        } else {
            Box::new(children.non_blanket_impls.iter().flat_map(|(_, v)| v.iter()))
        };
        let candidates = children.blanket_impls.iter().chain(nonblanket).copied();

        Box::new(candidates.filter(|&child| {
            let infcx = self.infcx.fork();
            let args = infcx.fresh_args_for_item(DUMMY_SP, child);
            let trait_ref_child =
                self.tcx.impl_trait_ref(child).instantiate(self.tcx, args).skip_normalization();
            infcx
                .at(&ObligationCause::dummy(), self.param_env)
                .eq(DefineOpaqueTypes::Yes, trait_ref_child, self.trait_ref)
                .is_ok()
        }))
    }

    fn traverse_descendants(
        &self,
        start_node: DefId,
        mut action: impl FnMut(DefId) -> GraphTraversalAction,
    ) -> bool {
        let mut stack: Vec<DefId> = self.matching_children(start_node).collect();
        while let Some(node) = stack.pop() {
            match action(node) {
                GraphTraversalAction::Skip => (),
                GraphTraversalAction::Traverse => stack.extend(self.matching_children(node)),
                GraphTraversalAction::Interrupt => return false,
            }
        }
        true
    }

    // Compute whether we know all the nodes that may unify with `self.trait_ref``.
    // We take inspiration from rustc_next_solver::cohenrence::trait_ref_is_knowable,
    // but ignore future-compatibility.
    fn remote_crates_allow_impls(&self) -> bool {
        let trait_ref = remove_unnameable_for_orphan_check(self.tcx, self.trait_ref);
        orphan_check_trait_ref(&self.infcx, trait_ref, InCrate::Remote, |ty| Ok::<_, !>(ty))
            .unwrap()
            .is_ok()
    }
}

// The orphan check crashes if it encounters unnameable types,
// so we replace them with equivalent ones. This is fine because this is a syntactic check.
fn remove_unnameable_for_orphan_check<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
) -> ty::TraitRef<'tcx> {
    struct Folder<'tcx>(TyCtxt<'tcx>);

    impl<'tcx> TypeFolder<TyCtxt<'tcx>> for Folder<'tcx> {
        fn cx(&self) -> TyCtxt<'tcx> {
            self.0
        }

        fn fold_ty(&mut self, t: Ty<'tcx>) -> Ty<'tcx> {
            match t.kind() {
                ty::FnDef(..) | ty::Closure(..) | ty::CoroutineClosure(..) | ty::Coroutine(..) => {
                    // Unnameable types are considered extern types by `orphan_check_trait_ref` in `InCrate::Remote` mode,
                    // so we replace them with unit as a dummy extern type.
                    Ty::new_unit(self.cx())
                }
                _ => t.super_fold_with(self),
            }
        }
    }

    trait_ref.fold_with(&mut Folder(tcx))
}
