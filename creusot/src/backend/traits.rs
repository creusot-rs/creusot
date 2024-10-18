use super::{clone_map::Dependencies, term::lower_pure, Why3Generator};
use crate::{
    backend,
    backend::{all_generic_decls_for, own_generic_decls_for, Namer},
    ctx::ItemType,
    util::{self, item_name, module_name},
};
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{GenericArgs, GenericArgsRef};
use why3::declaration::{Decl, Goal, Module, TyDecl};

pub(crate) fn lower_impl<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Module {
    let tcx = ctx.tcx;
    let data = ctx.trait_impl(def_id).clone();

    let mut names = Dependencies::new(ctx, [def_id]);

    let mut decls: Vec<_> = own_generic_decls_for(&mut names, def_id).collect();
    let mut refn_decls = Vec::new();

    for refn in &data.refinements {
        let name = item_name(tcx, refn.impl_.0, Namespace::ValueNS);

        decls.extend(own_generic_decls_for(&mut names, refn.impl_.0));
        refn_decls.push(Decl::Goal(Goal {
            name: format!("{}_refn", &*name).into(),
            goal: lower_pure(ctx, &mut names, &refn.refn.clone()),
        }));
    }

    let clones = names.provide_deps(ctx);
    decls.extend(clones);
    decls.extend(refn_decls);

    let attrs = Vec::from_iter(ctx.span_attr(ctx.def_span(def_id)));
    let meta = ctx.display_impl_of(def_id);
    Module { name: module_name(ctx.tcx, def_id).to_string().into(), decls, attrs, meta }
}

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_assoc_ty(&mut self, def_id: DefId) -> Module {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);

        let mut names = Dependencies::new(self, [def_id]);

        let mut decls: Vec<_> = all_generic_decls_for(&mut names, def_id).collect();
        let ty_decl = self.assoc_ty_decl(
            &mut names,
            def_id,
            GenericArgs::identity_for_item(self.tcx, def_id),
        );

        decls.push(ty_decl);

        let clones = names.provide_deps(self);
        decls.extend(clones);

        let attrs = Vec::from_iter(self.span_attr(self.def_span(def_id)));
        let meta = self.display_impl_of(def_id);

        Module { name: module_name(self.tcx, def_id).to_string().into(), decls, attrs, meta }
    }

    // Probably needs to take a pair of id and subst to handle cloning properly
    pub(crate) fn assoc_ty_decl<N: Namer<'tcx>>(
        &mut self,
        names: &mut N,
        def_id: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> Decl {
        let ty_name = names.ty(def_id, substs).as_ident();
        let ty_params = vec![];

        let ty_decl = match self.tcx.associated_item(def_id).container {
            rustc_middle::ty::ImplContainer => {
                let assoc_ty = self.tcx.type_of(def_id).instantiate_identity();
                TyDecl::Alias {
                    ty_name,
                    ty_params,
                    alias: backend::ty::translate_ty(self, names, rustc_span::DUMMY_SP, assoc_ty),
                }
            }
            rustc_middle::ty::TraitContainer => TyDecl::Opaque { ty_name, ty_params },
        };

        Decl::TyDecl(ty_decl)
    }
}
