use super::{
    clone_map2::{CloneLevel, Namer},
    term::lower_pure,
    Cloner,
};
use crate::{
    ctx::TranslationCtx,
    translation::function::own_generic_decls_for,
    util::{item_name, module_name},
};
use creusot_rustc::{hir::def_id::DefId, resolve::Namespace};
use why3::declaration::{Decl, Goal, Module};

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
