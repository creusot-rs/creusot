use crate::{
    backend::{
        DefKind, Why3Generator,
        clone_map::Namer,
        logic::function_call,
        term::{lower_condition, lower_pure},
        ty::translate_ty,
    },
    contracts_items::{should_replace_trigger, why3_attrs},
    translation::specification::{PreContract, PreSignature},
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident,
    coma::{Param, Prototype},
    declaration::{Contract, Signature},
    exp::Trigger,
};

/// The signature of a program function
#[derive(Debug, Clone)]
pub(crate) struct ProgramSignature {
    /// Signature of the corresponding coma handler
    pub(crate) prototype: Prototype,
    pub(crate) contract: Contract,
    /// Return type of the function
    pub(crate) return_ty: why3::ty::Type,
    pub(crate) variant: Option<(why3::Exp, why3::ty::Type)>,
}

/// Translates a Rust (program) function signature to a coma signature.
///
/// Note that `pre_sig` should be normalized!
pub(crate) fn lower_program_sig<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    mut pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
    return_ident: Ident,
) -> ProgramSignature {
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

    let variant =
        pre_sig.contract.variant.take().map(|term| {
            (lower_pure(ctx, names, &term), translate_ty(ctx, names, term.span, term.ty))
        });
    let contract = lower_contract(ctx, names, pre_sig.contract);

    ProgramSignature { prototype: Prototype { name, attrs, params }, contract, return_ty, variant }
}

/// The signature of a logical function
#[derive(Debug, Clone)]
pub(crate) struct LogicSignature {
    pub(crate) why_sig: Signature,
    pub(crate) variant: Option<why3::Exp>,
}

/// Translates a Pearlite (logical) function signature to a whyml signature.
///
/// Note that `pre_sig` should be normalized!
pub(crate) fn lower_logic_sig<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    mut pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
) -> LogicSignature {
    let span = ctx.tcx.def_span(def_id);
    let args: Box<[(Ident, _)]> = pre_sig
        .inputs
        .iter()
        .map(|&(id, span, ty)| (id.0, translate_ty(ctx, names, span, ty)))
        .collect();

    let mut attrs = if ctx.def_kind(def_id) == DefKind::ConstParam {
        vec![]
    } else {
        why3_attrs(ctx.tcx, def_id)
    };

    if let Some(attr) =
        def_id.as_local().map(|d| ctx.def_span(d)).and_then(|span| ctx.span_attr(span))
    {
        attrs.push(attr)
    }

    let retty = if names.normalize(pre_sig.output).is_bool() {
        None
    } else {
        Some(translate_ty(ctx, names, span, pre_sig.output))
    };
    let variant = pre_sig.contract.variant.take().map(|term| lower_pure(ctx, names, &term));
    let contract = lower_contract(ctx, names, pre_sig.contract);

    let mut sig = Signature { name, trigger: None, attrs, retty, args, contract };
    if ctx.opts.simple_triggers
        && (ctx.def_kind(def_id) == DefKind::ConstParam || should_replace_trigger(ctx.tcx, def_id))
    {
        sig.trigger = Some(Trigger::single(function_call(&sig)))
    };
    LogicSignature { why_sig: sig, variant }
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
    Contract { requires, ensures }
}
