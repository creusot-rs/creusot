use crate::{
    backend::{
        Namer, Why3Generator,
        logic::function_call,
        term::{lower_condition, lower_pure},
        ty::translate_ty,
    },
    contracts_items::{should_replace_trigger, why3_attrs},
    naming::ident_of,
    specification::PreSignature,
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident,
    coma::{Param, Prototype},
    declaration::{Contract, Signature},
    exp::{Binder, Trigger},
};

/// Translates a Rust (program) function signature to a coma signature.
///
/// Note that `pre_sig` should be normalized!
///
/// # Return
///
/// - The signature of the corresponding coma handler
/// - The contract of the function
/// - The return type of the function
pub(crate) fn lower_program_sig<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
) -> (Prototype, Contract, why3::ty::Type) {
    let span = ctx.tcx.def_span(def_id);
    let return_ty = translate_ty(ctx, names, span, pre_sig.output);
    let params: Box<[Param]> = pre_sig
        .inputs
        .iter()
        .map(|(id, span, ty)| Param::Term(ident_of(*id), translate_ty(ctx, names, *span, *ty)))
        .chain([Param::Cont(
            "return".into(),
            [].into(),
            [Param::Term("ret".into(), return_ty.clone())].into(),
        )])
        .collect();

    let mut attrs = why3_attrs(ctx.tcx, def_id);

    if let Some(attr) =
        def_id.as_local().map(|d| ctx.def_span(d)).and_then(|span| ctx.span_attr(span))
    {
        attrs.push(attr)
    }

    let requires = pre_sig
        .contract
        .requires
        .into_iter()
        .map(|cond| lower_condition(ctx, names, cond))
        .collect();
    let ensures = pre_sig
        .contract
        .ensures
        .into_iter()
        .map(|cond| lower_condition(ctx, names, cond))
        .collect();
    let variant = pre_sig.contract.variant.map(|term| lower_pure(ctx, names, &term));

    (Prototype { name, attrs, params }, Contract { requires, ensures, variant }, return_ty)
}

/// Translates a Pearlite (logical) function signature to a whyml signature.
///
/// Note that `pre_sig` should be normalized!
pub(crate) fn lower_logic_sig<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
) -> Signature {
    let span = ctx.tcx.def_span(def_id);
    let args: Box<[Binder]> = pre_sig
        .inputs
        .iter()
        .map(|(id, span, ty)| Binder::typed(ident_of(*id), translate_ty(ctx, names, *span, *ty)))
        .collect();

    let mut attrs = why3_attrs(ctx.tcx, def_id);

    if let Some(attr) =
        def_id.as_local().map(|d| ctx.def_span(d)).and_then(|span| ctx.span_attr(span))
    {
        attrs.push(attr)
    }

    let retty = Some(translate_ty(ctx, names, span, pre_sig.output));

    let requires = pre_sig
        .contract
        .requires
        .into_iter()
        .map(|cond| lower_condition(ctx, names, cond))
        .collect();
    let ensures = pre_sig
        .contract
        .ensures
        .into_iter()
        .map(|cond| lower_condition(ctx, names, cond))
        .collect();
    let variant = pre_sig.contract.variant.map(|term| lower_pure(ctx, names, &term));
    let contract = Contract { requires, ensures, variant };

    let mut sig = Signature { name, trigger: None, attrs, retty, args, contract };
    if ctx.opts.simple_triggers && should_replace_trigger(ctx.tcx, def_id) {
        sig.trigger = Some(Trigger::single(function_call(&sig)))
    };
    sig
}
