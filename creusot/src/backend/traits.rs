use crate::{
    backend::{Why3Generator, clone_map::Dependencies, is_trusted_item, term::lower_pure},
    contracts_items::is_snapshot_deref,
    ctx::FileModule,
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident,
    declaration::{Decl, Goal, Module},
};

pub(crate) fn lower_impl<'tcx>(ctx: &Why3Generator<'tcx>, def_id: DefId) -> Vec<FileModule> {
    if is_trusted_item(ctx.tcx, def_id) {
        return vec![];
    }

    let data = ctx.trait_impl(def_id).clone();
    let mut res = vec![];

    for refn in &data.refinements {
        let impl_did = refn.impl_.0;

        // HACK: Snapshot::deref is a (very) special case, do not generate refinement obligations for it.
        if is_snapshot_deref(ctx.tcx, impl_did) {
            continue;
        }

        let mut names = Dependencies::new(ctx, impl_did);
        let goal = lower_pure(ctx, &mut names, &refn.refn.clone());
        if goal.is_true() {
            continue;
        }
        let (mut decls, setters) = names.provide_deps(ctx);
        let refines = Ident::fresh(ctx.crate_name(), "refines");
        decls.push(Decl::Goal(Goal { name: refines, goal }));

        let attrs = ctx.span_attr(ctx.def_span(impl_did)).into_iter().collect();
        let meta = ctx.display_impl_of(impl_did);
        let mut path = ctx.module_path(impl_did);
        path.add_suffix("__refines");
        let name = path.why3_ident();
        res.push(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
    }

    res
}
