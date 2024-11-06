use super::{clone_map::Dependencies, term::lower_pure, Why3Generator};
use crate::naming::module_name;
use rustc_hir::def_id::DefId;
use why3::declaration::{Decl, Goal, Module};

pub(crate) fn lower_impl<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> Vec<Module> {
    let data = ctx.trait_impl(def_id).clone();
    let mut res = vec![];

    for refn in &data.refinements {
        let impl_did = refn.impl_.0;
        let mut names = Dependencies::new(ctx, impl_did);
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
