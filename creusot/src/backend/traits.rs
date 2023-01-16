use super::term::lower_pure;

use crate::{
    clone_map::{CloneLevel, CloneMap},
    ctx::TranslationCtx,
    translation::{
        function::{all_generic_decls_for, own_generic_decls_for},
        ty,
    },
    util::{self, item_name, module_name, ItemType},
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::AssocItemContainer::*;
use rustc_resolve::Namespace;
use why3::declaration::{Decl, Goal, Module, TyDecl};

pub(crate) fn lower_impl<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Module {
    let tcx = ctx.tcx;
    let data = ctx.trait_impl(def_id).clone();

    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Body);

    let mut impl_decls = Vec::new();
    for refn in &data.refinements {
        let name = item_name(tcx, refn.impl_.0, Namespace::ValueNS);

        impl_decls.extend(own_generic_decls_for(tcx, refn.impl_.0));
        impl_decls.push(Decl::Goal(Goal {
            name: format!("{}_refn", &*name).into(),
            goal: lower_pure(ctx, &mut names, refn.refn.clone()),
        }));
    }

    let mut decls: Vec<_> = own_generic_decls_for(ctx.tcx, def_id).collect();
    decls.extend(names.to_clones(ctx));
    decls.extend(impl_decls);

    Module { name: module_name(ctx.tcx, def_id), decls }
}

pub(crate) fn translate_assoc_ty<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Module {
    assert_eq!(util::item_type(ctx.tcx, def_id), ItemType::AssocTy);

    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Body);

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    let name = item_name(ctx.tcx, def_id, Namespace::TypeNS);

    let ty_decl = match ctx.tcx.associated_item(def_id).container {
        ImplContainer => {
            let assoc_ty = ctx.tcx.type_of(def_id);
            TyDecl::Alias {
                ty_name: name.clone(),
                ty_params: vec![],
                alias: ty::translate_ty(ctx, &mut names, rustc_span::DUMMY_SP, assoc_ty),
            }
        }
        TraitContainer => TyDecl::Opaque { ty_name: name.clone(), ty_params: vec![] },
    };

    decls.extend(names.to_clones(ctx));
    decls.push(Decl::TyDecl(ty_decl));

    Module { name: module_name(ctx.tcx, def_id), decls }
}
