use why3::declaration::Module;

use crate::{clone_map::CloneMap, ctx::TranslationCtx, util};

use rustc_hir::def_id::DefId;

fn interface_for(ctx: &mut TranslationCtx<'_, '_>, def_id: DefId) -> Module {
	let mut names = CloneMap::new(ctx.tcx);

	let sig = util::signature_of(ctx, &mut names, def_id);
	todo!()
}