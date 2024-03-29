use super::{clone_map::Dependencies, CloneSummary, Why3Generator};
use crate::{backend::signature::signature_of, ctx::*};
use rustc_hir::def_id::DefId;

// TODO: Remove entirely, but it seems like there's an issue
// in the dependency calcuation for program functions
pub(crate) fn interface_for<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> CloneSummary<'tcx> {
    let mut names = Dependencies::new(ctx.tcx, [def_id]);
    let _ = signature_of(ctx, &mut names, def_id);
    let (_, summary) = names.provide_deps(ctx, GraphDepth::Shallow);

    summary
}
