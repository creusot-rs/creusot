use super::{clone_map::Dependencies, term::lower_pure, Why3Generator};
use crate::{
    backend::Namer,
    ctx::ItemType,
    util::{self, erased_identity_for_item, module_name},
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArgsRef;
use why3::declaration::{Decl, Goal, Module, TyDecl};

pub(crate) fn lower_impl<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Vec<Module> {
    let data = ctx.trait_impl(def_id).clone();
    let mut res = vec![];

    for refn in &data.refinements {
        let impl_did = refn.impl_.0;
        let mut names = Dependencies::new(ctx, [impl_did]);
        let goal = lower_pure(ctx, &mut names, &refn.refn.clone());
        let mut decls = names.provide_deps(ctx);
        decls.push(Decl::Goal(Goal { name: "refines".into(), goal }));

        let attrs = Vec::from_iter(ctx.span_attr(ctx.def_span(impl_did)));
        let meta = ctx.display_impl_of(impl_did);
        res.push(Module {
            name: (module_name(ctx.tcx, impl_did).to_string() + "__refines").into(),
            decls,
            attrs,
            meta,
        })
    }

    res
}

impl<'tcx> Why3Generator<'tcx> {
    pub(crate) fn translate_assoc_ty(&mut self, def_id: DefId) -> Module {
        assert_eq!(util::item_type(self.tcx, def_id), ItemType::AssocTy);

        let mut names = Dependencies::new(self, [def_id]);

        let mut decls = vec![self.assoc_ty_decl(
            &mut names,
            def_id,
            erased_identity_for_item(self.tcx, def_id),
        )];
        decls.extend(names.provide_deps(self));

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
            rustc_middle::ty::ImplContainer => unreachable!("should be normalized"),
            rustc_middle::ty::TraitContainer => TyDecl::Opaque { ty_name, ty_params },
        };

        Decl::TyDecl(ty_decl)
    }
}
