use std::collections::HashMap;

use creusot_rustc::{
    hir::def_id::DefId,
    middle::ty::{
        subst::SubstsRef, AssocItemContainer::*, EarlyBinder, ParamEnv, TraitRef, TyCtxt,
    },
    resolve::Namespace,
    trait_selection::traits::ImplSource,
};

use why3::{
    declaration::{Decl, Goal, Module, TyDecl},
    exp::Exp,
};

use crate::{
    rustc_extensions, translation::function::terminator::evaluate_additional_predicates, util,
};

use crate::{
    ctx::*,
    translation::ty::{self, translate_ty},
    util::{ident_of, inputs_and_output, is_law, is_spec, item_type},
};

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

    pub(crate) fn translate_impl(&mut self, impl_id: DefId) -> TranslatedItem {
        let trait_ref = self.tcx.impl_trait_ref(impl_id).unwrap();
        self.translate_trait(trait_ref.def_id);

        // Impl Refinement module
        let mut decls: Vec<_> = own_generic_decls_for(self.tcx, impl_id).collect();
        let mut names = CloneMap::new(self.tcx, impl_id, CloneLevel::Body);

        // names.param_env(param_env);
        let mut laws = Vec::new();
        let implementor_map = self.tcx.impl_item_implementor_ids(impl_id);

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

            self.translate(impl_item);

            let subst = InternalSubsts::identity_for_item(self.tcx, impl_item);
            names.insert(impl_item, subst);

            decls.extend(own_generic_decls_for(self.tcx, impl_item));

            let refn_subst = subst.rebase_onto(self.tcx, impl_id, trait_ref.substs);

            // TODO: Clean up and abstract
            let predicates = self
                .extern_spec(trait_item)
                .map(|p| p.predicates_for(self.tcx, refn_subst))
                .unwrap_or_else(Vec::new);

            use creusot_rustc::{
                infer::infer::TyCtxtInferExt,
                trait_selection::traits::error_reporting::InferCtxtExt,
            };
            self.tcx.infer_ctxt().enter(|infcx| {
                let res = evaluate_additional_predicates(
                    &infcx,
                    predicates,
                    self.param_env(impl_item),
                    self.def_span(impl_item),
                );
                if let Err(errs) = res {
                    let body_id = self.tcx.hir().body_owned_by(impl_item.expect_local());
                    infcx.report_fulfillment_errors(&errs, Some(body_id), false);
                    self.crash_and_error(creusot_rustc::span::DUMMY_SP, "error above");
                }
            });

            let refinement = names.insert(trait_item, refn_subst);

            refinement.add_dep(self.tcx, self.tcx.item_name(impl_item), (impl_item, subst));
            refinement.opaque();

            // Since we don't have contracts of logic functions in the interface and we can't substitute the definition in
            // the implementation module, we must recreate the spec axiom by hand here.
            if matches!(item_type(self.tcx, trait_item), ItemType::Logic | ItemType::Predicate) {
                let contract = contract_of(self, trait_item);

                if !contract.is_empty() {
                    let axiom =
                        logic_refinement(self, &mut names, impl_item, trait_item, refn_subst);
                    decls.extend(names.to_clones(self));
                    decls.push(Decl::Goal(axiom));
                }
            }
        }

        decls.extend(names.to_clones(self));
        TranslatedItem::Impl { modl: Module { name: module_name(self, impl_id), decls } }
    }

    pub(crate) fn translate_assoc_ty(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);

        let mut names = CloneMap::new(self.tcx, def_id, CloneLevel::Interface);

        let mut decls: Vec<_> = all_generic_decls_for(self.tcx, def_id).collect();
        let name = item_name(self.tcx, def_id, Namespace::TypeNS);

        let ty_decl = match self.tcx.associated_item(def_id).container {
            creusot_rustc::middle::ty::ImplContainer => names.with_public_clones(|names| {
                let assoc_ty = self.tcx.type_of(def_id);
                TyDecl::Alias {
                    ty_name: name.clone(),
                    ty_params: vec![],
                    alias: ty::translate_ty(self, names, creusot_rustc::span::DUMMY_SP, assoc_ty),
                }
            }),
            creusot_rustc::middle::ty::TraitContainer => {
                TyDecl::Opaque { ty_name: name.clone(), ty_params: vec![] }
            }
        };

        decls.extend(names.to_clones(self));
        decls.push(Decl::TyDecl(ty_decl));

        (Module { name: module_name(self, def_id), decls }, names.summary())
    }
}

fn logic_refinement<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &mut CloneMap<'tcx>,
    impl_item_id: DefId,
    trait_item_id: DefId,
    refn_subst: SubstsRef<'tcx>,
) -> Goal {
    // Get the contract of the trait version
    let trait_contract = names.with_public_clones(|names| {
        let pre_contract = crate::specification::contract_of(ctx, trait_item_id);
        let param_env = ctx.param_env(impl_item_id);
        EarlyBinder(pre_contract)
            .subst(ctx.tcx, refn_subst)
            .normalize(ctx.tcx, param_env)
            .to_exp(ctx, names)
    });

    let impl_contract = names.with_public_clones(|names| {
        let pre_contract = crate::specification::contract_of(ctx, impl_item_id);
        pre_contract.to_exp(ctx, names)
    });

    let (trait_inps, _) = inputs_and_output(ctx.tcx, trait_item_id);
    let (impl_inps, output) = inputs_and_output(ctx.tcx, impl_item_id);

    let span = ctx.tcx.def_span(impl_item_id);
    let mut args = Vec::new();
    let mut subst = HashMap::new();
    names.with_public_clones(|names| {
        for (ix, ((id, _), (id2, ty))) in trait_inps.zip(impl_inps).enumerate() {
            let ty = translate_ty(ctx, names, span, ty);
            let id =
                if id.name.is_empty() { format!("_{}'", ix + 1).into() } else { ident_of(id.name) };
            let id2 = if id2.name.is_empty() {
                format!("_{}'", ix + 1).into()
            } else {
                ident_of(id2.name)
            };
            args.push((id.clone(), ty));
            subst.insert(id2, Exp::pure_var(id));
        }
    });

    let mut impl_precond = impl_contract.requires_conj();
    impl_precond.subst(&subst);
    let trait_precond = trait_contract.requires_conj();

    let mut impl_postcond = impl_contract.ensures_conj();
    impl_postcond.subst(&subst);
    let trait_postcond = trait_contract.ensures_conj();

    let retty = names.with_public_clones(|names| translate_ty(ctx, names, span, output));
    let post_refn =
        Exp::Forall(vec![("result".into(), retty)], box impl_postcond.implies(trait_postcond));

    let mut refn = trait_precond.implies(impl_precond).log_and(post_refn);
    refn = if args.is_empty() { refn } else { Exp::Forall(args, box refn) };

    // Don't use `item_name` here
    let name = item_name(ctx.tcx, impl_item_id, Namespace::ValueNS);

    Goal { name: format!("{}_spec", &*name).into(), goal: refn }
}

pub(crate) fn associated_items(tcx: TyCtxt, def_id: DefId) -> impl Iterator<Item = &AssocItem> {
    tcx.associated_items(def_id)
        .in_definition_order()
        .filter(move |item| !is_spec(tcx, item.def_id))
}

use crate::function::{all_generic_decls_for, own_generic_decls_for};
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

use super::specification::contract_of;

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
            use creusot_rustc::trait_selection::infer::TyCtxtInferExt;

            if !leaf_def.is_final() && trait_ref.still_further_specializable() {
                return Some((def_id, substs));
            }
            // Translate the original substitution into one on the selected impl method
            let leaf_substs = tcx.infer_ctxt().enter(|infcx| {
                let param_env = param_env.with_reveal_all_normalized(tcx);
                let substs = substs.rebase_onto(tcx, trait_def_id, impl_data.substs);
                let substs = creusot_rustc::trait_selection::traits::translate_substs(
                    &infcx,
                    param_env,
                    impl_data.impl_def_id,
                    substs,
                    leaf_def.defining_node,
                );
                infcx.tcx.erase_regions(substs)
            });

            Some((leaf_def.item.def_id, leaf_substs))
        }
        ImplSource::Param(_, _) => Some((def_id, substs)),
        ImplSource::Closure(impl_data) => Some((impl_data.closure_def_id, impl_data.substs)),
        _ => unimplemented!(),
    }
}
