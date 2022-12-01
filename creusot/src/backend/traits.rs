use super::clone_map2::Namer;
use crate::ctx::TranslationCtx;
use creusot_rustc::hir::def_id::DefId;
use why3::declaration::Module;

fn lower_impl<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    priors: Namer<'_, 'tcx>,
    def_id: DefId,
) -> Module {
    let data = ctx.trait_impl(def_id);


}
