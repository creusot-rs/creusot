use super::{clone_map::Dependencies, term::lower_pure, Why3Generator};
use crate::{
    backend::{self, all_generic_decls_for, own_generic_decls_for, Namer},
    contracts_items,
    ctx::ItemType,
    translated_item::FileModule,
    util::{self, item_name, module_name},
};
use rustc_hir::{def::Namespace, def_id::DefId};
use rustc_middle::ty::{GenericArgs, GenericArgsRef};
use why3::declaration::{Decl, Goal, Module, TyDecl};

pub(crate) fn lower_impl<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> FileModule {
    let tcx = ctx.tcx;
    let data = ctx.trait_impl(def_id).clone();

    let mut names = Dependencies::new(ctx, [def_id]);

    let mut decls: Vec<_> = own_generic_decls_for(ctx.tcx, def_id).collect();
    let mut refn_decls = Vec::new();

    for refn in &data.refinements {
        let name = item_name(tcx, refn.impl_.0, Namespace::ValueNS);

        decls.extend(own_generic_decls_for(tcx, refn.impl_.0));
        // HACK: Snapshot::deref is a (very) special case, do not generate refinement obligations for it.
        if !contracts_items::is_snapshot_deref(ctx.tcx, refn.impl_.0) {
            refn_decls.push(Decl::Goal(Goal {
                name: format!("{}_refn", &*name).into(),
                goal: lower_pure(ctx, &mut names, &refn.refn.clone()),
            }));
        }
    }

    let clones = names.provide_deps(ctx);
    decls.extend(clones);
    decls.extend(refn_decls);

    let attrs = Vec::from_iter(ctx.span_attr(ctx.def_span(def_id)));
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id, util::NS::M);
    let name = path.why3_ident();
    FileModule { path, modl: Module { name, decls, attrs, meta } }
}

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_assoc_ty(&mut self, def_id: DefId) -> Module {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);

        let mut names = Dependencies::new(self, [def_id]);

        let mut decls: Vec<_> = all_generic_decls_for(self.tcx, def_id).collect();
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
