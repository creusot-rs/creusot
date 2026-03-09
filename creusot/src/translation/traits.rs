use crate::{
    backend::ty_inv::sig_add_type_invariant_spec,
    contracts_items::{is_law, is_pearlite, is_sealed, is_spec},
    ctx::*,
    naming::name,
    translation::pearlite::{PIdent, Substable, Term, TermKind},
    util::erased_identity_for_item,
    very_stable_hash::get_very_stable_hash,
};
use rustc_hir::def_id::DefId;
use rustc_infer::{
    infer::{InferCtxt, TyCtxtInferExt},
    traits::{Obligation, ObligationCause, TraitEngine},
};
use rustc_middle::ty::{
    EarlyBinder, GenericArgsRef, ParamEnv, Predicate, Ty, TypingEnv, TypingMode,
};
use rustc_span::Span;
use rustc_trait_selection::{
    error_reporting::InferCtxtErrorExt,
    traits::{FulfillmentError, TraitEngineExt},
};
use std::collections::HashMap;

#[derive(Clone)]
pub(crate) struct Refinement<'tcx> {
    pub(crate) impl_item: DefId,
    pub(crate) refn: Refn<'tcx>,
}

/// `PRE1 ==> ... ==> PREn ==> POST`
/// We keep `PRE` and `POST` separate to allow inserting const setters.
#[derive(Debug, Clone)]
pub(crate) struct Refn<'tcx> {
    pub(crate) args: Vec<(PIdent, Ty<'tcx>, Span)>,
    pub(crate) pre: Vec<Term<'tcx>>,
    pub(crate) post: Term<'tcx>,
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
        assert!(self.impl_opt_trait_id(impl_id).is_some(), "{impl_id:?} is not a trait impl");
        let trait_ref = self.impl_trait_ref(impl_id).instantiate_identity().skip_normalization();

        let implementor_map = self.tcx.impl_item_implementor_ids(impl_id);

        let mut refinements = Vec::new();
        let mut implementor_map =
            self.with_stable_hashing_context(|mut hcx| implementor_map.to_sorted(&mut hcx, true));
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
) -> Refn<'tcx> {
    let typing_env = TypingEnv::non_body_analysis(ctx.tcx, impl_item_id);

    // Get the contract of the trait version
    let mut trait_sig = EarlyBinder::bind(ctx.sig(trait_item_id).clone())
        .instantiate(ctx.tcx, refn_subst)
        .skip_normalization()
        .normalize_contract(ctx, typing_env);

    let mut impl_sig = ctx.sig(impl_item_id).clone();

    if !is_pearlite(ctx.tcx, impl_item_id) {
        sig_add_type_invariant_spec(ctx, typing_env, impl_item_id, &mut trait_sig, trait_item_id);
        sig_add_type_invariant_spec(ctx, typing_env, impl_item_id, &mut impl_sig, impl_item_id);
    }

    let span = ctx.tcx.def_span(impl_item_id);
    let mut args = Vec::new();
    let mut subst = HashMap::new();
    for (&(id, span, _), (id2, _, ty)) in trait_sig.inputs.iter().zip(impl_sig.inputs.iter()) {
        args.push((id, *ty, span));
        subst.insert(id2.0, TermKind::Var(id));
    }

    let mut impl_precond = impl_sig.contract.requires_conj(ctx.tcx);
    impl_precond.subst(&subst);
    let trait_precond = trait_sig.contract.requires();

    let mut impl_postcond = impl_sig.contract.ensures_conj(ctx.tcx);
    impl_postcond.subst(&subst);
    let trait_postcond = trait_sig.contract.ensures_conj(ctx.tcx);

    let retty = impl_sig.output;

    let post_refn =
        impl_postcond.implies(trait_postcond).forall((name::result().into(), retty)).span(span);

    // refn = args.into_iter().rfold(refn, |acc, r| acc.forall(r).span(span));

    Refn { args, pre: trait_precond, post: impl_precond.conj(post_refn) }
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
    let errors = fulfill_cx.evaluate_obligations_error_on_ambiguity(infcx);
    if !errors.is_empty() { Err(errors) } else { Ok(()) }
}
