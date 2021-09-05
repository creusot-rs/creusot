use rustc_hir::{def_id::DefId, Constness};
use rustc_middle::traits::Reveal;
use rustc_middle::ty::{
    // fold::BoundVarsCollector,
    subst::SubstsRef,
    AssocKind,
    Binder,
    Instance,
    ParamEnv,
    PredicateKind,
    TraitPredicate,
    TraitRef,
    TyCtxt,
    TypeFoldable,
};
use why3::declaration::CloneKind;
use why3::{
    declaration::{CloneSubst, Decl, DeclClone, Module, ValKind::*},
    mlcfg::Type,
    QName,
};

use crate::ctx;

use crate::ctx::*;
use crate::util::is_contract;

use rustc_resolve::Namespace;

impl<'tcx> TranslationCtx<'_, 'tcx> {
    // Translate a trait declaration
    pub fn translate_trait(&mut self, def_id: DefId) {
        if !self.translated_items.insert(def_id) {
            return;
        }

        let mut names = CloneMap::new(self.tcx);

        // The first predicate is a trait reference so we skip it
        for super_trait in traits_used_by(self.tcx, def_id).filter(|t| t.def_id() != def_id) {
            // Ensure trait depends on all super traits
            translate_constraint(self, &mut names, super_trait);
        }

        let mut trait_decls = Vec::new();
        for item in self.tcx.associated_items(def_id).in_definition_order() {
            match item.kind {
                AssocKind::Fn => {
                    if is_contract(self.tcx, item.def_id) {
                        continue;
                    }

                    let mut sig = crate::util::signature_of(self, &mut names, item.def_id);

                    trait_decls.extend(crate::translation::function::own_generic_decls_for(
                        self.tcx,
                        item.def_id,
                    ));

                    if crate::is_predicate(self.tcx, item.def_id) {
                        sig.retty = None;
                        trait_decls.push(Decl::ValDecl(Predicate { sig }));
                    } else {
                        trait_decls.push(Decl::ValDecl(Val { sig }));
                    }
                }
                knd => unimplemented!("{:?} - {:?}", def_id, knd),
            }
        }

        let mut decls: Vec<_> = super::prelude_imports(true);
        decls.extend(own_generic_decls_for(self.tcx, def_id));
        decls.extend(names.to_clones(self));
        decls.extend(trait_decls);

        let trait_name = translate_trait_name(self.tcx, def_id);


        self.functions.insert(def_id, Module { name: trait_name.name(), decls });
    }
}

pub fn translate_constraint<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    names: &mut CloneMap<'tcx>,
    tp: TraitPredicate<'tcx>,
) {
    names.name_for_mut(tp.def_id(), tp.trait_ref.substs);

    // If we haven't seen this trait, first translate it
    ctx.translate_trait(tp.def_id());
}

use crate::function::{all_generic_decls_for, own_generic_decls_for};
use rustc_middle::ty::subst::InternalSubsts;

pub fn translate_impl(ctx: &mut TranslationCtx<'_, '_>, impl_id: DefId) {
    if !ctx.translated_items.insert(impl_id) {
        return;
    }

    let trait_ref = ctx.tcx.impl_trait_ref(impl_id).unwrap();
    let mut names = CloneMap::new(ctx.tcx);

    ctx.translate_trait(trait_ref.def_id);

    let mut subst = ctx::type_param_subst(ctx, &mut names, trait_ref.def_id, trait_ref.substs);

    for assoc in ctx.tcx.associated_items(impl_id).in_definition_order() {
        let assoc_subst = InternalSubsts::identity_for_item(ctx.tcx, impl_id);
        let name = names.name_for_mut(assoc.def_id, assoc_subst);

        ctx.translate_function(assoc.def_id);

        // Get the id of the generic version of the trait method
        let trait_method = ctx
            .tcx
            .associated_items(trait_ref.def_id)
            .find_by_name_and_namespace(
                ctx.tcx,
                assoc.ident,
                Namespace::ValueNS, //TODO generalize this to include associated types
                trait_ref.def_id,
            )
            .unwrap();

        // build the substitution between the concrete and generic versions
        let method_subst = ctx
            .tcx
            .generics_of(trait_method.def_id)
            .params
            .iter()
            .zip(ctx.tcx.generics_of(assoc.def_id).params.iter())
            .map(|(tr_param, inst_param)| {
                CloneSubst::Type(
                    (&*tr_param.name.as_str().to_lowercase()).into(),
                    Type::TConstructor(QName {
                        module: vec![name.clone()],
                        name: inst_param.name.as_str().to_lowercase(),
                    }),
                )
            });

        subst.extend(method_subst);

        if crate::is_predicate(ctx.tcx, assoc.def_id) {
            subst.push(CloneSubst::Predicate(
                assoc.ident.to_string().into(),
                names.qname_for_mut(assoc.def_id, assoc_subst)
                // crate::ctx::translate_value_id(ctx.tcx, assoc.def_id),
            ));
        } else {
            subst.push(CloneSubst::Val(
                assoc.ident.to_string().into(),
                names.qname_for_mut(assoc.def_id, assoc_subst)
                // crate::ctx::translate_value_id(ctx.tcx, assoc.def_id),
            ));
        }
    }

    let mut decls: Vec<_> = super::prelude_imports(true);
    decls.extend(all_generic_decls_for(ctx.tcx, impl_id));
    decls.extend(names.to_clones(ctx));

    decls.push(Decl::Clone(DeclClone {
        name: translate_trait_name(ctx.tcx, trait_ref.def_id),
        subst,
        kind: CloneKind::Bare,
    }));

    let name = translate_value_id(ctx.tcx, impl_id);
    ctx.functions.insert(impl_id, Module { name: name.name(), decls });
}

fn translate_trait_name(tcx: TyCtxt<'_>, def_id: DefId) -> QName {
    translate_value_id(tcx, def_id)
}

pub fn traits_used_by<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> impl Iterator<Item = TraitPredicate<'tcx>> {
    let predicates = tcx.predicates_of(def_id);

    predicates.predicates.iter().filter_map(|(pred, _)| {
        let inner = pred.kind().no_bound_vars().unwrap();
        use rustc_middle::ty::PredicateKind::*;
        match inner {
            Trait(tp, _) => Some(tp),
            _ => None,
        }
    })
}

use crate::rustc_extensions::*;
use rustc_middle::ty::GenericParamDefKind;

// Find the instance that will be used for `trait_meth_id` given the substitution `subst`.
// If no instance is found (either because it does not exist or is ambiguous) then it returns `Option`.
pub fn resolve_instance_opt<'tcx>(
    tcx: TyCtxt<'tcx>,
    inside_of: DefId,
    trait_meth_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Option<Option<Instance<'tcx>>> {
    let generics = tcx.generics_of(inside_of);
    let trait_id =
        tcx.trait_of_item(trait_meth_id).expect("resolve_instance_opt: expected associated item");
    let predicates = (0..generics.count()).filter_map(|i| {
        let param_def = generics.param_at(i, tcx);
        match param_def.kind {
            GenericParamDefKind::Lifetime | GenericParamDefKind::Const { .. } => return None,
            _ => {}
        };

        let subst = tcx.mk_substs([tcx.mk_param_from_def(param_def)].iter());
        let trait_ref = TraitRef::new(trait_id, subst);
        let trait_pred = PredicateKind::Trait(TraitPredicate { trait_ref }, Constness::NotConst);
        let mut bound_vars_collector = BoundVarsCollector::new();
        trait_pred.visit_with(&mut bound_vars_collector);
        let trait_binder = Binder::bind_with_vars(trait_pred, bound_vars_collector.into_vars(tcx));
        Some(tcx.mk_predicate(trait_binder))
    });

    let base_predicates = tcx.predicates_of(inside_of).instantiate_identity(tcx).predicates;
    let predicates = tcx.mk_predicates(base_predicates.into_iter().chain(predicates));
    let param_env = ParamEnv::new(predicates, Reveal::UserFacing);
    let inst = resolve_instance(tcx, param_env.and((trait_meth_id, subst)));

    match inst {
        Err(mut e) => {
            e.cancel();
            None
        }
        Ok(i) => Some(i),
    }
}
