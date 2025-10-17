use super::pearlite::{Term, TermKind};
use crate::{
    backend::ty_inv::sig_add_type_invariant_spec,
    contracts_items::{is_law, is_pearlite, is_sealed, is_spec},
    ctx::*,
    naming::name,
    util::erased_identity_for_item,
    very_stable_hash::get_very_stable_hash,
};
use rustc_hir::def_id::DefId;
use rustc_infer::{
    infer::{DefineOpaqueTypes, InferCtxt, TyCtxtInferExt},
    traits::{
        CodegenObligationError, Obligation, ObligationCause, TraitEngine,
        specialization_graph::Graph,
    },
};
use rustc_middle::ty::{
    Const, ConstKind, EarlyBinder, GenericArgsRef, ParamConst, ParamEnv, ParamEnvAnd, ParamTy,
    Predicate, TraitRef, Ty, TyCtxt, TyKind, TypeFoldable, TypeFolder, TypingEnv, TypingMode,
};
use rustc_span::{DUMMY_SP, ErrorGuaranteed, Span};
use rustc_trait_selection::{
    error_reporting::InferCtxtErrorExt,
    traits::{FulfillmentError, ImplSource, InCrate, TraitEngineExt, orphan_check_trait_ref},
};
use rustc_type_ir::{
    TypeSuperFoldable,
    fast_reject::{TreatParams, simplify_type},
};
use std::{collections::HashMap, iter};

#[derive(Clone)]
pub(crate) struct Refinement<'tcx> {
    pub(crate) impl_item: DefId,
    pub(crate) refn: Term<'tcx>,
}

impl<'tcx> TranslationCtx<'tcx> {
    pub(crate) fn laws_inner(&self, trait_or_impl: DefId) -> Vec<DefId> {
        self.tcx
            .associated_items(trait_or_impl)
            .in_definition_order()
            .map(|item| item.def_id)
            .filter(|&did| !is_spec(self.tcx, did) && is_law(self.tcx, did))
            .collect()
    }

    pub(crate) fn translate_impl(&self, impl_id: DefId) -> Vec<Refinement<'tcx>> {
        assert!(self.trait_id_of_impl(impl_id).is_some(), "{impl_id:?} is not a trait impl");
        let trait_ref = self.impl_trait_ref(impl_id).unwrap().instantiate_identity();

        let implementor_map = self.tcx.impl_item_implementor_ids(impl_id);

        let mut refinements = Vec::new();
        let mut implementor_map =
            self.with_stable_hashing_context(|hcx| implementor_map.to_sorted(&hcx, true));
        implementor_map.sort_by_cached_key(|(trait_item, impl_item)| {
            get_very_stable_hash(&[**trait_item, **impl_item] as &[_], &self.tcx)
        });
        for (&trait_item, &impl_item) in implementor_map {
            // Don't generate refinements for impls that come from outside crates
            if !impl_id.is_local() || !self.def_kind(trait_item).is_fn_like() {
                continue;
            }

            let subst = erased_identity_for_item(self.tcx, impl_item);
            let refn_subst = subst.rebase_onto(self.tcx, impl_id, trait_ref.args);

            // TODO: Clean up and abstract
            let predicates = self
                .extern_spec(trait_item)
                .map(|p| p.predicates_for(self.tcx, refn_subst))
                .unwrap_or_else(Vec::new);

            let infcx = self.infer_ctxt().ignoring_regions().build(TypingMode::non_body_analysis());

            let res = evaluate_additional_predicates(
                &infcx,
                predicates,
                self.param_env(impl_item),
                self.def_span(impl_item),
            );
            if let Err(errs) = res {
                infcx.err_ctxt().report_fulfillment_errors(errs);
                continue;
            }

            let Ok(mut ancestors) = self.trait_def(trait_ref.def_id).ancestors(self.tcx, impl_id)
            else {
                continue;
            };
            assert!(ancestors.next().unwrap().def_id() == impl_id);

            if let Some(leaf) = ancestors.leaf_def(self.tcx, trait_item) {
                if is_sealed(self.tcx, leaf.item.def_id) {
                    self.error(
                        self.def_span(impl_item),
                        "This trait methods overrides a sealed implementation.",
                    )
                    .emit();
                    self.error(
                        self.def_span(leaf.item.def_id),
                        "This sealed implementation is overriden.",
                    )
                    .emit();
                }
            }

            let refn = logic_refinement_term(self, impl_item, trait_item, refn_subst);
            refinements.push(Refinement { impl_item, refn });
        }

        refinements
    }
}

fn logic_refinement_term<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    impl_item_id: DefId,
    trait_item_id: DefId,
    refn_subst: GenericArgsRef<'tcx>,
) -> Term<'tcx> {
    let typing_env = TypingEnv::non_body_analysis(ctx.tcx, impl_item_id);

    // Get the contract of the trait version
    let mut trait_sig = EarlyBinder::bind(ctx.sig(trait_item_id).clone())
        .instantiate(ctx.tcx, refn_subst)
        .normalize(ctx, typing_env);

    let mut impl_sig = ctx.sig(impl_item_id).clone();

    if !is_pearlite(ctx.tcx, impl_item_id) {
        sig_add_type_invariant_spec(ctx, typing_env, impl_item_id, &mut trait_sig, trait_item_id);
        sig_add_type_invariant_spec(ctx, typing_env, impl_item_id, &mut impl_sig, impl_item_id);
    }

    let span = ctx.tcx.def_span(impl_item_id);
    let mut args = Vec::new();
    let mut subst = HashMap::new();
    for (&(id, _, _), (id2, _, ty)) in trait_sig.inputs.iter().zip(impl_sig.inputs.iter()) {
        args.push((id, *ty));
        subst.insert(id2.0, TermKind::Var(id));
    }

    let mut impl_precond = impl_sig.contract.requires_conj(ctx.tcx);
    impl_precond.subst(&subst);
    let trait_precond = trait_sig.contract.requires_conj(ctx.tcx);

    let mut impl_postcond = impl_sig.contract.ensures_conj(ctx.tcx);
    impl_postcond.subst(&subst);
    let trait_postcond = trait_sig.contract.ensures_conj(ctx.tcx);

    let retty = impl_sig.output;

    let post_refn =
        impl_postcond.implies(trait_postcond).forall((name::result().into(), retty)).span(span);

    let mut refn = trait_precond.implies(impl_precond.conj(post_refn));
    refn = args.into_iter().rfold(refn, |acc, r| acc.forall(r).span(span));

    refn
}

pub(crate) fn evaluate_additional_predicates<'tcx>(
    infcx: &InferCtxt<'tcx>,
    p: Vec<Predicate<'tcx>>,
    param_env: ParamEnv<'tcx>,
    sp: Span,
) -> Result<(), Vec<FulfillmentError<'tcx>>> {
    let mut fulfill_cx = <dyn TraitEngine<'tcx, _>>::new(infcx);
    for predicate in p {
        let predicate = infcx.tcx.erase_and_anonymize_regions(predicate);
        let cause = ObligationCause::dummy_with_span(sp);
        let obligation = Obligation { cause, param_env, recursion_depth: 0, predicate };
        fulfill_cx.register_predicate_obligation(infcx, obligation);
    }
    let errors = fulfill_cx.select_all_or_error(infcx);
    if !errors.is_empty() { Err(errors) } else { Ok(()) }
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
#[derive(Debug, Clone, Copy)]
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
    /// We don't know if an instance exists.
    UnknownNotFound,
    /// We know that no instance exists.
    ///
    /// For example, in `fn<T> f(x: T) { let _ = x.clone() }`, we  don't have an
    /// instance for `T::clone` until we know more about `T`.
    NoInstance,
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
        let trait_ref = tcx.normalize_erasing_regions(typing_env, trait_ref);

        let source = tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref));
        if let Err(err) = source {
            if let CodegenObligationError::Ambiguity = err {
                // FIXME: if there are several instances available, `codegen_select_candidate`
                // returns an error, while we would like it to return any of the instances.
                // We need to find another entry point of the trait solver.
                // In the meantime, pretend that we have an instance that we do not know
                return TraitResolved::UnknownFound;
            }

            // We have not found an instance. Does there exist a specializing instance?

            let Ok(gt) = GraphTraversal::new(tcx, typing_env.param_env, trait_ref) else {
                // Error => return dummy value
                return TraitResolved::UnknownNotFound;
            };

            if gt.remote_crates_allow_impls() {
                // A downstream or cousin crate is allowed to implement some
                // generic parameters of this trait-ref.
                return TraitResolved::UnknownNotFound;
            }

            // Check whether one of the descendents of start_node applies too
            let r = gt.traverse_descendants(trait_ref.def_id, |node| {
                if tcx.defaultness(node).is_default() {
                    GraphTraversalAction::Traverse
                } else {
                    // This final instance may match our trait_ref
                    GraphTraversalAction::Interrupt
                }
            });
            if r {
                // We have not found an instance in the graph
                return TraitResolved::NoInstance;
            } else {
                return TraitResolved::UnknownNotFound;
            };
        };
        trace!("TraitResolved::resolve {source:?}",);

        match source.unwrap() {
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

                unimplemented!(
                    "Cannot handle builtin implementation of `{}` for `{}`",
                    tcx.def_path_str(trait_ref.def_id),
                    substs.type_at(0)
                )
            }
        }
    }

    pub(crate) fn to_opt(
        self,
        did: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> Option<(DefId, GenericArgsRef<'tcx>)> {
        match self {
            TraitResolved::Instance { def, impl_: _ } => Some(def),
            TraitResolved::NotATraitItem | TraitResolved::UnknownFound => Some((did, substs)),
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
                self.tcx.impl_trait_ref(child).unwrap().instantiate(self.tcx, args);
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
        orphan_check_trait_ref(&self.infcx, self.trait_ref, InCrate::Remote, |ty| Ok::<_, !>(ty))
            .unwrap()
            .is_ok()
    }
}
