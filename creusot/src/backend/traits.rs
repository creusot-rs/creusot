use super::term::lower_pure;
use crate::{
    clone_map::{CloneLevel, CloneMap},
    ctx::TranslationCtx,
    translation::function::own_generic_decls_for,
    util::{item_name, module_name},
};
use rustc_hir::def_id::DefId;

use rustc_resolve::Namespace;
use why3::declaration::{Decl, Goal, Module};

pub(crate) fn lower_impl<'tcx>(ctx: &mut TranslationCtx<'tcx>, def_id: DefId) -> Module {
    let tcx = ctx.tcx;
    let data = ctx.trait_impl(def_id).clone();

    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Body);

    let mut impl_decls = Vec::new();
    for refn in &data.refinements {
        let name = item_name(tcx, refn.impl_.0, Namespace::ValueNS);

        impl_decls.extend(own_generic_decls_for(tcx, refn.impl_.0));
        impl_decls.push(Decl::Goal(Goal {
            name: format!("{}_refn", &*name).into(),
            goal: lower_pure(ctx, &mut names, refn.refn.clone()),
        }));
    }

    let mut decls: Vec<_> = own_generic_decls_for(ctx.tcx, def_id).collect();
    let (clones, _) = names.to_clones(ctx);
    decls.extend(clones);
    decls.extend(impl_decls);

    Module { name: module_name(ctx.tcx, def_id), decls }
}
