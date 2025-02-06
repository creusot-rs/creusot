use rustc_hir::def_id::DefId;
use why3::{
    declaration::{Contract, Signature},
    exp::{Binder, Trigger},
    Ident,
};

use crate::{
    backend,
    contracts_items::{should_replace_trigger, why3_attrs},
    naming::{anonymous_param_symbol, ident_of},
    specification::{Condition, PreSignature},
    translation::specification::PreContract,
};

use super::{logic::function_call, term::lower_pure, Namer, Why3Generator};

#[derive(Debug, Clone)]
#[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct PreSignature2 {
    pub name: Ident,
    pub trigger: Option<Trigger>, // None means we should use the "simple_trigger"
    pub attrs: Vec<why3::declaration::Attribute>,
    pub retty: Option<why3::ty::Type>,
    pub args: Vec<(Ident, why3::ty::Type)>,
    pub contract: Contract,
}

impl From<PreSignature2> for Signature {
    fn from(sig: PreSignature2) -> Self {
        Signature {
            name: sig.name,
            trigger: sig.trigger,
            attrs: sig.attrs,
            retty: sig.retty,
            args: sig.args.into_iter().map(|(id, ty)| Binder::typed(id, ty)).collect(),
            contract: sig.contract,
        }
    }
}

pub(crate) fn signature_of<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    def_id: DefId,
) -> PreSignature2 {
    debug!("signature_of {def_id:?}");
    let pre_sig = ctx.sig(def_id).clone();
    sig_to_why3(ctx, names, name, pre_sig, def_id)
}

pub(crate) fn sig_to_why3<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    name: Ident,
    pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
) -> PreSignature2 {
    let contract = contract_to_why3(pre_sig.contract, ctx, names);

    let span = ctx.tcx.def_span(def_id);
    let args: Vec<_> = pre_sig
        .inputs
        .iter()
        .enumerate()
        .map(|(ix, (id, _, ty))| {
            let ty = backend::ty::translate_ty(ctx, names, span, *ty);
            let id = if id.is_empty() {
                anonymous_param_symbol(ix).as_str().into()
            } else {
                ident_of(*id)
            };
            (Ident::fresh(id), ty)
        })
        .collect();

    let mut attrs = why3_attrs(ctx.tcx, def_id);

    def_id
        .as_local()
        .map(|d| ctx.def_span(d))
        .and_then(|span| ctx.span_attr(span))
        .map(|attr| attrs.push(attr));

    let retty = backend::ty::translate_ty(ctx, names, span, pre_sig.output);

    let mut sig = PreSignature2 { name, trigger: None, attrs, retty: Some(retty), args, contract };
    let trigger = if ctx.opts.simple_triggers && should_replace_trigger(ctx.tcx, def_id) {
        Some(Trigger::single(function_call(&sig)))
    } else {
        None
    };
    sig.trigger = trigger;
    sig
}

fn lower_condition<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    cond: Condition<'tcx>,
) -> why3::declaration::Condition {
    why3::declaration::Condition { exp: lower_pure(ctx, names, &cond.term), expl: cond.expl }
}

fn contract_to_why3<'tcx, N: Namer<'tcx>>(
    pre: PreContract<'tcx>,
    ctx: &Why3Generator<'tcx>,
    names: &N,
) -> Contract {
    let mut out = Contract::new();
    for cond in pre.requires.into_iter() {
        out.requires.push(lower_condition(ctx, names, cond));
    }
    for cond in pre.ensures.into_iter() {
        out.ensures.push(lower_condition(ctx, names, cond));
    }
    if let Some(term) = &pre.variant {
        out.variant = vec![lower_pure(ctx, names, &term)];
    }

    out
}
