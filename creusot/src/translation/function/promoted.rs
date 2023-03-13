use crate::{
    ctx::TranslationCtx,
    translation::{fmir, function::LocalIdent, specification::PreContract},
    util::PreSignature,
};
use rustc_hir::def_id::DefId;
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
    ctx: &mut TranslationCtx<'tcx>,
    body: &Body<'tcx>,
    parent: DefId,
) -> CreusotResult<(PreSignature<'tcx>, fmir::Body<'tcx>)> {
    let func_translator = BodyTranslator::build_context(ctx.tcx, ctx, &body, parent);
    let fmir = func_translator.translate();

    let sig = promoted_signature(body);

    Ok((sig, fmir))
}
