use crate::{
    backend::{
        Namer, Why3Generator,
        logic::function_call,
        term::{lower_condition, lower_pure},
        ty::translate_ty,
    },
    contracts_items::{should_replace_trigger, why3_attrs},
    specification::{PreContract, PreSignature},
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident,
    coma::{Param, Prototype},
    declaration::{Contract, Signature},
    exp::Trigger,
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
    return_ident: Ident,
) -> (Prototype, Contract, why3::ty::Type) {
    let span = ctx.tcx.def_span(def_id);
    let return_ty = translate_ty(ctx, names, span, pre_sig.output);
    let params: Box<[Param]> = pre_sig
        .inputs
        .iter()
        .map(|(id, span, ty)| Param::Term(id.0, translate_ty(ctx, names, *span, *ty)))
        .chain([Param::Cont(
            return_ident,
            [].into(),
            [Param::Term(Ident::fresh_local("x"), return_ty.clone())].into(),
        )])
        .collect();

    let mut attrs = why3_attrs(ctx.tcx, def_id);
    if let Some(attr) =
        def_id.as_local().map(|d| ctx.def_span(d)).and_then(|span| ctx.span_attr(span))
    {
        attrs.push(attr)
    }

    let contract = lower_contract(ctx, names, pre_sig.contract);

    (Prototype { name, attrs, params }, contract, return_ty)
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
    let args: Box<[(Ident, _)]> = pre_sig
        .inputs
        .iter()
        .map(|&(id, span, ty)| (id.0, translate_ty(ctx, names, span, ty)))
        .collect();

    let mut attrs = why3_attrs(ctx.tcx, def_id);

    if let Some(attr) =
        def_id.as_local().map(|d| ctx.def_span(d)).and_then(|span| ctx.span_attr(span))
    {
        attrs.push(attr)
    }

    let retty = Some(translate_ty(ctx, names, span, pre_sig.output));
    let contract = lower_contract(ctx, names, pre_sig.contract);

    let mut sig = Signature { name, trigger: None, attrs, retty, args, contract };
    if ctx.opts.simple_triggers && should_replace_trigger(ctx.tcx, def_id) {
        sig.trigger = Some(Trigger::single(function_call(&sig)))
    };
    sig
}

pub(crate) fn lower_contract<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    contract: PreContract<'tcx>,
) -> Contract {
    let requires =
        contract.requires.into_iter().map(|cond| lower_condition(ctx, names, cond)).collect();
    let ensures =
        contract.ensures.into_iter().map(|cond| lower_condition(ctx, names, cond)).collect();
    let variant = contract.variant.map(|term| lower_pure(ctx, names, &term));
    Contract { requires, ensures, variant }
}
