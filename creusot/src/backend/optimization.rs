mod constant_propagation;
mod invariants;
mod useless_goto;

use crate::{
    ctx::{BodyId, TranslationCtx},
    translation::fmir::Body,
};

/// Various optimizations performed on fMIR:
/// - constant propagation
/// - inference of prophetic invariants
/// - remove useless gotos
pub(crate) fn optimizations<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &mut Body<'tcx>,
    body_id: BodyId,
) {
    constant_propagation::propagate_constants(body);
    invariants::infer_proph_invariants(ctx, body, body_id);
    useless_goto::remove_useless_gotos(body);
}
