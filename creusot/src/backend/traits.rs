use crate::{
    backend::{
        Why3Generator, clone_map::Dependencies, common_meta_decls, is_trusted_item,
        term::lower_pure,
    },
    contracts_items::get_namespace_ty,
    ctx::FileModule,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::GenericArgsRef;
use why3::{
    Ident,
    declaration::{Decl, Goal, Module},
};

pub(crate) fn lower_impl(ctx: &Why3Generator<'_>, def_id: DefId) -> Vec<FileModule> {
    if is_trusted_item(ctx.tcx, def_id) {
        return vec![];
    }

    let mut res = vec![];

    for refn in ctx.trait_impl(def_id) {
        let impl_did = refn.impl_item;

        let names = Dependencies::new(ctx, impl_did);
        let namespace_ty =
            names.def_ty_no_dependency(get_namespace_ty(ctx.ctx.tcx), GenericArgsRef::default());
        let goal = lower_pure(ctx, &names, &refn.refn);
        if goal.is_true() {
            continue;
        }
        let mut decls = names.provide_deps(ctx);
        decls.extend(common_meta_decls());
        decls.push(Decl::Goal(Goal { name: Ident::fresh(ctx.crate_name(), "refines"), goal }));

        if ctx.used_namespaces.get() {
            let mut new_decls = ctx.generate_namespace_type(namespace_ty);
            new_decls.extend(std::mem::take(&mut decls));
            decls = new_decls;
        }

        let attrs = ctx.span_attr(ctx.def_span(impl_did)).into_iter().collect();
        let meta = ctx.display_impl_of(impl_did);
        let mut path = ctx.module_path(impl_did);
        path.add_suffix("__refines");
        let name = path.why3_ident();
        res.push(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
    }

    res
}
