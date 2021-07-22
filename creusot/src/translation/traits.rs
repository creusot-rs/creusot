use heck::SnakeCase;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{
    subst::InternalSubsts,
    AssocKind, GenericParamDefKind, TraitPredicate, TyCtxt,
};
use why3::{declaration::{CloneSubst, Signature, Contract, Decl, DeclClone, Module, TyDecl, Val}, mlcfg::{LocalIdent, QName}};

use super::{NameMap, TranslationCtx};

impl<'tcx> TranslationCtx<'_, 'tcx> {
    // pub fn clone_traits(
    //     &mut self,
    //     name_map: &mut NameMap<'tcx>,
    //     def_id: DefId,
    // ) -> Vec<why3::declaration::Decl> {
    //     let traits = traits_used_by(self.tcx, def_id);

    //     let mut clone_traits = Vec::new();
    //     for t in traits {
    //         self.translate_trait(t.def_id());
    //         clone_traits.push(self.clone_item(name_map, t.def_id(), t.trait_ref.substs));
    //     }
    //     clone_traits
    // }

    // Translate a trait declaration
    pub fn translate_trait(&mut self, def_id: DefId) {
        if !self.used_traits.insert(def_id) {
            return;
        }

        let mut names = NameMap::new(self.tcx);

        let trait_name = translate_trait_name(self.tcx, def_id);
        let mut decls : Vec<_> = super::generic_decls_for(self.tcx, def_id).collect();

        // The first predicate is a trait reference so we skip it
        for super_trait in traits_used_by(self.tcx, def_id)
            .filter(|t| t.def_id() != def_id)
        {
            self.translate_trait(super_trait.def_id());
            decls.push(translate_constraint(self, &mut names, super_trait));
        }
        self.modules.add_module(Module {
            name: trait_name.name(),
            decls: decls,
        })
    }
}

fn translate_constraint<'tcx>(ctx: &mut TranslationCtx<'_, 'tcx>, names: &mut NameMap<'tcx>, tp: TraitPredicate<'tcx>) -> Decl {
    // let trait_name = translate_trait_name(ctx.tcx, tp.def_id());
    let (_, clone_name) = names.name_for(tp.def_id(), tp.trait_ref.substs);

    ctx.clone_item(tp.def_id(), tp.trait_ref.substs, clone_name.clone())
}

    // pub fn translate_trait(&mut self, def_id: DefId) {
    //     let mut name_map = NameMap::new(self.tcx);

    //     if self.used_traits.contains(&def_id) {
    //         return;
    //     } else {
    //         self.used_traits.insert(def_id);
    //     }
    //     let mut trait_name = translate_trait_name(self.tcx, def_id);
    //     // let params = self.tcx.generics_of(def_id);
    //     let mut param_tys = generic_decls_of(self.tcx, def_id);

    //     let mut supers = self.clone_traits(&mut name_map, def_id);
    //     supers.remove(0); // HACK: REMOVE THIS
    //     param_tys.append(&mut supers);

    //     for item in self.tcx.associated_items(def_id).in_definition_order() {
    //         match item.kind {
    //             AssocKind::Fn => {
    //                 let fn_sig = self.tcx.fn_sig(item.def_id).skip_binder();

    //                 let inputs = self
    //                     .tcx
    //                     .fn_arg_names(item.def_id)
    //                     .iter()
    //                     .zip(fn_sig.inputs().iter())
    //                     .map(|(name, ty)| {
    //                         (
    //                             name.to_string().into(),
    //                             super::ty::translate_ty(self, rustc_span::DUMMY_SP, ty),
    //                         )
    //                     })
    //                     .collect();
    //                 let output =
    //                     super::ty::translate_ty(self, rustc_span::DUMMY_SP, fn_sig.output());

    //                 let name = super::translate_value_id(self.tcx, item.def_id);
    //                 param_tys.push(Decl::ValDecl(Val {
    //                     sig: Signature { name, contract: Contract::new(), args: inputs, retty: Some(output) }
    //                 }))
    //             }
    //             AssocKind::Type => unimplemented!("associated type"),
    //             AssocKind::Const => unimplemented!("constants"),
    //         }
    //     }

    //     let trait_mod = Module { name: trait_name.name(), decls: param_tys };
    //     self.modules.add_module(trait_mod);
    // }

    // pub fn translate_impl(&mut self, trait_id: DefId, impl_id: DefId) -> Decl {
    //     let mut name_map = NameMap::new(self.tcx);

    //     let mut impl_decls = generic_decls_of(self.tcx, impl_id);

    //     let trait_ref = self.tcx.impl_trait_ref(impl_id).unwrap(); // yolo
    //     let mut trait_subst = self.type_param_subst(trait_id, trait_ref.substs);

    //     for meth in self.tcx.associated_items(impl_id).in_definition_order() {
    //         let id_subst = InternalSubsts::identity_for_item(self.tcx, meth.def_id);
    //         impl_decls.push(self.clone_item(&mut name_map, meth.def_id, id_subst));
    //         let (_, clone_name) = name_map.name_for(meth.def_id, id_subst);

    //         trait_subst.push(CloneSubst::Val(
    //             LocalIdent::Name(meth.ident.to_string()),
    //             QName { module: vec![clone_name], name: "impl".into() },
    //         ))
    //     }


    //     impl_decls.push(Decl::Clone(DeclClone {
    //         name: translate_trait_name(self.tcx, trait_id),
    //         subst: trait_subst,
    //         as_nm: None,
    //     }));

    //     let impl_name = translate_trait_name(self.tcx, impl_id).name();
    //     Decl::Module(Module { name: impl_name, decls: impl_decls })
    // }




fn translate_trait_name(tcx: TyCtxt<'_>, def_id: DefId) -> QName {
    super::translate_value_id(tcx, def_id)
}

pub fn traits_used_by<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> impl Iterator<Item = TraitPredicate<'tcx>> {
    let predicates = tcx.predicates_of(def_id);

    predicates.predicates.iter().filter_map(|(pred, _)| {
        let inner = pred.kind().no_bound_vars().unwrap();
        use rustc_middle::ty::PredicateKind::*;
        match inner {
            Trait(tp, _) => Some(tp),
            _ => None
        }
    })
}
