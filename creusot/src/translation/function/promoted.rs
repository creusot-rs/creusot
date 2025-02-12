use crate::{
    ctx::{BodyId, TranslationCtx},
    translation::{fmir, function::LocalIdent, specification::PreContract},
    util::PreSignature,
};
use rustc_middle::mir::Body;

use crate::error::CreusotResult;

use super::BodyTranslator;

pub(crate) fn promoted_signature<'tcx>(body: &Body<'tcx>) -> PreSignature<'tcx> {
    let inputs = body
        .args_iter()
        .map(|arg| {
            let info = &body.local_decls[arg];
            (LocalIdent::anon(arg).symbol(), info.source_info.span, info.ty)
        })
        .collect();

    PreSignature { contract: PreContract::default(), inputs, output: body.return_ty() }
}

pub(crate) fn translate_promoted<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body_id: BodyId,
) -> CreusotResult<(PreSignature<'tcx>, fmir::Body<'tcx>)> {
    let body = ctx.body(body_id).clone();
    let fmir = BodyTranslator::to_fmir(ctx.tcx, ctx, &body, body_id);

    let sig = promoted_signature(&body);

    Ok((sig, fmir))
}
