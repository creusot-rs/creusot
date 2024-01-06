use super::{
    clone_map::{CloneLevel, CloneMap, CloneSummary},
    term::lower_pure,
    CloneDepth, Why3Generator,
};
use crate::{
    backend,
    backend::{all_generic_decls_for, own_generic_decls_for},
    ctx::ItemType,
    util::{self, item_name, module_name},
};
use rustc_hir::{def::Namespace, def_id::DefId};
use why3::declaration::{Decl, Goal, Module, TyDecl};

pub(crate) fn lower_impl<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Module {
    let tcx = ctx.tcx;
    let data = ctx.trait_impl(def_id).clone();

    let mut names = CloneMap::new(ctx.tcx, def_id.into());

    let mut decls: Vec<_> = own_generic_decls_for(ctx.tcx, def_id).collect();
    let mut refn_decls = Vec::new();

    for refn in &data.refinements {
        let name = item_name(tcx, refn.impl_.0, Namespace::ValueNS);

        decls.extend(own_generic_decls_for(tcx, refn.impl_.0));
        refn_decls.push(Decl::Goal(Goal {
            name: format!("{}_refn", &*name).into(),
            goal: lower_pure(ctx, &mut names, refn.refn.clone()),
        }));
    }

    let (clones, _) = names.to_clones(ctx, CloneDepth::Deep);
    decls.extend(clones);
    decls.extend(refn_decls);

    Module { name: module_name(ctx.tcx, def_id), decls }
}

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_assoc_ty(&mut self, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);

        let mut names = CloneMap::new(self.tcx, def_id.into());

        let mut decls: Vec<_> = all_generic_decls_for(self.tcx, def_id).collect();
        let name = item_name(self.tcx, def_id, Namespace::TypeNS);

        let ty_decl = match self.tcx.associated_item(def_id).container {
            rustc_middle::ty::ImplContainer => names.with_vis(CloneLevel::Stub, |names| {
                let assoc_ty = self.tcx.type_of(def_id).subst_identity();
                TyDecl::Alias {
                    ty_name: name.clone(),
                    ty_params: vec![],
                    alias: backend::ty::translate_ty(self, names, rustc_span::DUMMY_SP, assoc_ty),
                }
            }),
            rustc_middle::ty::TraitContainer => {
                TyDecl::Opaque { ty_name: name.clone(), ty_params: vec![] }
            }
        };

        decls.push(Decl::TyDecl(ty_decl));

        let (clones, summary) = names.to_clones(self, CloneDepth::Shallow);
        decls.extend(clones);

        (Module { name: module_name(self.tcx, def_id), decls }, summary)
    }
}
