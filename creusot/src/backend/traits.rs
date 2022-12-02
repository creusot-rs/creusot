use super::{
    clone_map2::{CloneLevel, Namer},
    term::lower_pure,
    Cloner,
};
use crate::{
    backend::ty,
    ctx::TranslationCtx,
    translation::function::{all_generic_decls_for, own_generic_decls_for},
    util::{self, item_name, module_name, ItemType},
};
use creusot_rustc::{hir::def_id::DefId, resolve::Namespace};
use why3::declaration::{Decl, Goal, Module, TyDecl};

pub(crate) fn lower_impl<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    mut priors: Namer<'_, 'tcx>,
    def_id: DefId,
) -> Module {
    let tcx = ctx.tcx;
    let data = ctx.trait_impl(def_id).clone();

    let mut decls = priors.to_clones(ctx, CloneLevel::Body);

    for refn in &data.refinements {
        let name = item_name(tcx, refn.impl_.0, Namespace::ValueNS);

        decls.extend(own_generic_decls_for(tcx, refn.impl_.0));
        decls.push(Decl::Goal(Goal {
            name: format!("{}_spec", &*name).into(),
            goal: lower_pure(ctx, &mut priors, refn.refn.clone()),
        }));
    }

    Module { name: module_name(ctx, def_id), decls }

    // todo!()
}

pub(crate) fn translate_assoc_ty<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    mut priors: Namer<'_, 'tcx>,
    def_id: DefId,
) -> Module {
    assert_eq!(util::item_type(ctx.tcx, def_id), ItemType::AssocTy);

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    let name = item_name(ctx.tcx, def_id, Namespace::TypeNS);

    let ty_decl = match ctx.tcx.associated_item(def_id).container {
        creusot_rustc::middle::ty::ImplContainer => {
            let assoc_ty = ctx.tcx.type_of(def_id);
            TyDecl::Alias {
                ty_name: name.clone(),
                ty_params: vec![],
                alias: ty::translate_ty(ctx, &mut priors, creusot_rustc::span::DUMMY_SP, assoc_ty),
            }
        }
        creusot_rustc::middle::ty::TraitContainer => {
            TyDecl::Opaque { ty_name: name.clone(), ty_params: vec![] }
        }
    };

    decls.extend(priors.to_clones(ctx, CloneLevel::Interface));
    decls.push(Decl::TyDecl(ty_decl));

    Module { name: module_name(ctx, def_id), decls }
}
