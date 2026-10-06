use crate::{
    backend::{
        Why3Generator, common_meta_decls, module_context::Dependencies, term::lower_pure,
        ty::translate_ty,
    },
    ctx::FileModule,
};
use rustc_hir::def_id::DefId;
use why3::{Ident, declaration::Module};

pub(crate) fn lower_impl<'tcx>(ctx: &Why3Generator<'tcx>, def_id: DefId) -> Vec<FileModule> {
    let mut res = vec![];

    for refn in ctx.trait_impl(def_id) {
        let impl_did = refn.impl_item;

        let names = Dependencies::new(ctx, impl_did);
        let args: Vec<_> = refn
            .refn
            .args
            .iter()
            .map(|&(ident, ty, span)| (ident.0, translate_ty(ctx, &names, span, ty)))
            .collect();
        let pre = refn.refn.pre.iter().map(|t| lower_pure(ctx, &names, t)).collect::<Vec<_>>();
        let post = lower_pure(ctx, &names, &refn.refn.post);
        if pre.iter().any(|t| t.is_false()) || post.is_true() {
            continue;
        }
        let (mut decls, setters) = names.translate_deps(ctx);
        decls.extend(common_meta_decls());
        let name = Ident::fresh(ctx.crate_name(), "refines");
        decls.push(setters.mk_goal(name, args, pre.into_iter(), post));

        let attrs = ctx.span_attr(ctx.def_span(impl_did)).into_iter().collect();
        let meta = ctx.display_impl_of(impl_did);
        let mut path = ctx.module_path(impl_did);
        path.add_suffix("__refines");
        let name = path.why3_ident();
        res.push(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
    }

    res
}
