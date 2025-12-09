mod invariants;
mod remove_dead_locals;
mod simplify_temps;
mod useless_goto;

use rustc_hir::def_id::DefId;

use crate::{ctx::TranslationCtx, translation::fmir::Body};

/// Various optimizations performed on fMIR:
/// - constant propagation
/// - inference of prophetic invariants
/// - remove useless gotos
pub(crate) fn optimizations<'tcx>(ctx: &TranslationCtx<'tcx>, body: &mut Body<'tcx>, scope: DefId) {
    simplify_temps::simplify_temporaries(ctx, body);
    remove_dead_locals::remove_dead_locals(ctx, body);
    invariants::infer_invariant_places(ctx, body, scope);
    useless_goto::remove_useless_gotos(body);
}
