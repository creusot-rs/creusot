use crate::{
    ctx::*,
    rustc_extensions,
    translation::function::terminator::evaluate_additional_predicates,
    util::{inputs_and_output, is_law, is_spec, item_type},
};
use creusot_rustc::{
    hir::def_id::DefId,
    infer::infer::TyCtxtInferExt,
    middle::ty::{
        subst::SubstsRef, AssocItemContainer::*, EarlyBinder, ParamEnv, TraitRef, TyCtxt,
    },
    span::Symbol,
    trait_selection::traits::ImplSource,
};
use std::collections::HashMap;

#[derive(Clone)]
pub(crate) struct Refinement<'tcx> {
    pub(crate) trait_: (DefId, SubstsRef<'tcx>),
    pub(crate) impl_: (DefId, SubstsRef<'tcx>),
    pub(crate) refn: Term<'tcx>,
}

#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct TraitImpl<'tcx> {
    pub(crate) laws: Vec<DefId>,
    pub(crate) refinements: Vec<Refinement<'tcx>>,
}

impl<'tcx> TranslationCtx<'tcx> {
    // Translate a trait declaration
    pub(crate) fn translate_trait(&mut self, def_id: DefId) -> TranslatedItem {
        debug!("translating trait {def_id:?}");
        TranslatedItem::Trait {}
    }

    pub(crate) fn laws_inner(&self, trait_or_impl: DefId) -> Vec<DefId> {
        let mut laws = Vec::new();
        for item in associated_items(self.tcx, trait_or_impl) {
            if is_law(self.tcx, item.def_id) {
                laws.push(item.def_id);
            }
        }
        laws
    }

    pub(crate) fn translate_impl2(&mut self, impl_id: DefId) -> TraitImpl<'tcx> {
        assert!(self.trait_id_of_impl(impl_id).is_some(), "{impl_id:?} is not a trait impl");
        let trait_ref = self.tcx.impl_trait_ref(impl_id).unwrap();

        let mut laws = Vec::new();
        let implementor_map = self.tcx.impl_item_implementor_ids(impl_id);

        let mut refinements = Vec::new();
        for (&trait_item, &impl_item) in implementor_map {
            if is_law(self.tcx, trait_item) {
                laws.push(impl_item);
            }

            // Don't generate refinements for impls that come from outside crates
            if !impl_id.is_local() {
                continue;
            }

            // If there is no contract to refine, skip this item
            if contract_of(self, trait_item).is_empty() {
                continue;
            }

            let subst = InternalSubsts::identity_for_item(self.tcx, impl_item);

            let refn_subst = subst.rebase_onto(self.tcx, impl_id, trait_ref.substs);

            // TODO: Clean up and abstract
            let predicates = self
                .extern_spec(trait_item)
                .map(|p| p.predicates_for(self.tcx, refn_subst))
                .unwrap_or_else(Vec::new);

            let infcx = self.tcx.infer_ctxt().build();

            let res = evaluate_additional_predicates(
                &infcx,
                predicates,
                self.param_env(impl_item),
                self.def_span(impl_item),
            );
            use creusot_rustc::trait_selection::traits::error_reporting::TypeErrCtxtExt;
            if let Err(errs) = res {
                let body_id = self.tcx.hir().body_owned_by(impl_item.expect_local());
                infcx.err_ctxt().report_fulfillment_errors(&errs, Some(body_id));
                self.crash_and_error(creusot_rustc::span::DUMMY_SP, "error above");
            }

            // Since we don't have contracts of logic functions in the interface and we can't substitute the definition in
            // the implementation module, we must recreate the spec axiom by hand here.
            if matches!(item_type(self.tcx, trait_item), ItemType::Logic | ItemType::Predicate) {
                let contract = contract_of(self, trait_item);

                if !contract.is_empty() {
                    let axiom = logic_refinement_term(self, impl_item, trait_item, refn_subst);
                    refinements.push(Refinement {
                        trait_: (trait_item, refn_subst),
                        impl_: (impl_item, subst),
                        refn: axiom,
                    });
                }
            }
        }

        TraitImpl { laws, refinements }
    }
}

fn logic_refinement_term<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    impl_item_id: DefId,
    trait_item_id: DefId,
    refn_subst: SubstsRef<'tcx>,
) -> Term<'tcx> {
    // Get the contract of the trait version
    let trait_contract = {
        let pre_contract = contract_of(ctx, trait_item_id);
        let param_env = ctx.param_env(impl_item_id);
        EarlyBinder(pre_contract).subst(ctx.tcx, refn_subst).normalize(ctx.tcx, param_env)
    };

    let impl_contract = contract_of(ctx, impl_item_id);

    let (trait_inps, _) = inputs_and_output(ctx.tcx, trait_item_id);
    let (impl_inps, output) = inputs_and_output(ctx.tcx, impl_item_id);

    let span = ctx.tcx.def_span(impl_item_id);
    let mut args = Vec::new();
    let mut subst = HashMap::new();
    for (ix, ((id, _), (id2, ty))) in trait_inps.zip(impl_inps).enumerate() {
        let id =
            if id.name.is_empty() { Symbol::intern(&format!("_{}'", ix + 1)) } else { id.name };
        let id2 =
            if id2.name.is_empty() { Symbol::intern(&format!("_{}'", ix + 1)) } else { id2.name };
        args.push((id.clone(), ty));
        subst.insert(id2, Term { ty, kind: TermKind::Var(id), span });
    }

    let mut impl_precond = impl_contract.requires_conj(ctx.tcx);
    impl_precond.subst(&subst);
    let trait_precond = trait_contract.requires_conj(ctx.tcx);

    let mut impl_postcond = impl_contract.ensures_conj(ctx.tcx);
    impl_postcond.subst(&subst);
    let trait_postcond = trait_contract.ensures_conj(ctx.tcx);

    let retty = output;
    let post_refn = Term {
        kind: TermKind::Forall {
            binder: (Symbol::intern("result"), retty),
            body: box impl_postcond.implies(trait_postcond),
        },
        ty: ctx.tcx.types.bool,
        span,
    };

    let mut refn = trait_precond.implies(impl_precond).conj(post_refn);
    refn = if args.is_empty() {
        refn
    } else {
        args.into_iter().rfold(refn, |acc, r| Term {
            kind: TermKind::Forall { binder: r, body: box acc },
            ty: ctx.tcx.types.bool,
            span,
        })
    };

    refn
    // // Don't use `item_name` here
    // let name = item_name(ctx.tcx, impl_item_id, Namespace::ValueNS);

    // Goal { name: format!("{}_spec", &*name).into(), goal: refn }
}

pub(crate) fn associated_items(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = &AssocItem> {
    tcx.associated_items(def_id)
        .in_definition_order()
        .filter(move |item| !is_spec(tcx, item.def_id))
}

use creusot_rustc::middle::ty::{subst::InternalSubsts, AssocItem, Binder};

pub(crate) fn resolve_impl_source_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<ImplSource<'tcx, ()>> {
    trace!("resolve_impl_source_opt={def_id:?} {substs:?}");
    let substs = tcx.normalize_erasing_regions(param_env, substs);

    let trait_ref = if let Some(assoc) = tcx.opt_associated_item(def_id) {
        match assoc.container {
            ImplContainer => {
                EarlyBinder(tcx.impl_trait_ref(assoc.container_id(tcx))?).subst(tcx, substs)
            }
            TraitContainer => TraitRef { def_id: assoc.container_id(tcx), substs },
        }
    } else {
        if tcx.is_trait(def_id) {
            TraitRef { def_id, substs }
        } else {
            return None;
        }
    };

    let trait_ref = Binder::dummy(trait_ref);
    let source = rustc_extensions::codegen::codegen_fulfill_obligation(tcx, (param_env, trait_ref));

    match source {
        Ok(src) => Some(src),
        Err(err) => {
            trace!("resolve_impl_source_opt error");
            err.cancel();

            return None;
        }
    }
}

pub(crate) fn resolve_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    trace!("resolve_opt={def_id:?} {substs:?}");
    if tcx.is_trait(def_id) {
        resolve_trait_opt(tcx, param_env, def_id, substs)
    } else {
        resolve_assoc_item_opt(tcx, param_env, def_id, substs)
    }
}

pub(crate) fn resolve_trait_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    trace!("resolve_trait_opt={def_id:?} {substs:?}");
    if tcx.is_trait(def_id) {
        let impl_source = resolve_impl_source_opt(tcx, param_env, def_id, substs);
        debug!("impl_source={:?}", impl_source);
        match resolve_impl_source_opt(tcx, param_env, def_id, substs)? {
            ImplSource::UserDefined(impl_data) => Some((impl_data.impl_def_id, impl_data.substs)),
            ImplSource::Param(_, _) => Some((def_id, substs)),
            _ => None,
        }
    } else {
        None
    }
}

use creusot_rustc::middle::ty::AssocItemContainer;

use super::{
    pearlite::{Term, TermKind},
    specification::contract_of,
};

pub(crate) fn resolve_assoc_item_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    trace!("resolve_assoc_item_opt {:?} {:?}", def_id, substs);
    let assoc = tcx.opt_associated_item(def_id)?;

    // If we're given an associated item that is already on an instance,
    // we don't need to resolve at all!
    //
    // FIXME: not true given specialization!
    if let AssocItemContainer::ImplContainer = assoc.container {
        return None;
    }

    let trait_ref = TraitRef::from_method(tcx, tcx.trait_of_item(def_id).unwrap(), substs);
    use creusot_rustc::middle::ty::TypeVisitable;
    let source = resolve_impl_source_opt(tcx, param_env, def_id, substs)?;
    trace!("resolve_assoc_item_opt {source:?}",);

    match source {
        ImplSource::UserDefined(impl_data) => {
            let trait_def_id = tcx.trait_id_of_impl(impl_data.impl_def_id).unwrap();
            let trait_def = tcx.trait_def(trait_def_id);
            // Find the id of the actual associated method we will be running
            let leaf_def = trait_def
                .ancestors(tcx, impl_data.impl_def_id)
                .unwrap()
                // .leaf_def(tcx, assoc.ident, assoc.kind)
                .leaf_def(tcx, assoc.def_id)
                .unwrap_or_else(|| {
                    panic!("{:?} not found in {:?}", assoc, impl_data.impl_def_id);
                });

            if !leaf_def.is_final() && trait_ref.still_further_specializable() {
                return Some((def_id, substs));
            }

            // Translate the original substitution into one on the selected impl method
            let infcx = tcx.infer_ctxt().build();

            let param_env = param_env.with_reveal_all_normalized(tcx);
            let substs = substs.rebase_onto(tcx, trait_def_id, impl_data.substs);
            let substs = creusot_rustc::trait_selection::traits::translate_substs(
                &infcx,
                param_env,
                impl_data.impl_def_id,
                substs,
                leaf_def.defining_node,
            );
            let leaf_substs = infcx.tcx.erase_regions(substs);

            Some((leaf_def.item.def_id, leaf_substs))
        }
        ImplSource::Param(_, _) => Some((def_id, substs)),
        ImplSource::Closure(impl_data) => Some((impl_data.closure_def_id, impl_data.substs)),
        _ => unimplemented!(),
    }
}
