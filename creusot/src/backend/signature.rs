use std::cell::RefCell;

use rustc_hir::def_id::DefId;
use rustc_span::Symbol;
use why3::{
    Ident,
    declaration::{Condition as WCondition, Contract, Signature},
    exp::{Binder, Trigger},
};

use crate::{
    backend,
    contracts_items::{should_replace_trigger, why3_attrs},
    specification::{Condition, PreSignature},
    translation::specification::PreContract,
};

use super::{Namer, Why3Generator, logic::function_call, term::lower_pure};
use crate::pearlite::Renaming;

#[derive(Debug, Clone)]
// #[cfg_attr(feature = "serialize", derive(Serialize, Deserialize))]
pub struct PreSignature2 {
    pub name: Ident,
    pub trigger: Option<Trigger>, // None means we should use the "simple_trigger"
    pub attrs: Vec<why3::declaration::Attribute>,
    pub retty: Option<why3::ty::Type>,
    pub args: Vec<(Ident, why3::ty::Type)>,
    pub contract: Contract,
}

impl PreSignature2 {
    pub fn uses_simple_triggers(&self) -> bool {
        self.trigger.is_some()
    }
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
    let span = ctx.tcx.def_span(def_id);
    let args: Box<[Binder]> = pre_sig
        .inputs
        .into_iter()
        .map(|(ident, _, ty)| {
            let ty = backend::ty::translate_ty(ctx, names, span, ty);
            (ident, ty)
        })
        .collect();
    let renaming = todo!{}; // TODO get rid of this RefCell::new(args.iter().map(|(old, new, _)| (*old, *new)).collect());
    let contract = contract_to_why3(pre_sig.contract, ctx, &renaming, names);
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
    renaming: &RefCell<Renaming>,
    cond: Condition<'tcx>,
) -> WCondition {
    WCondition { exp: lower_pure(ctx, names, renaming, &cond.term), expl: cond.expl }
}

fn contract_to_why3<'tcx, N: Namer<'tcx>>(
    pre: PreContract<'tcx>,
    ctx: &Why3Generator<'tcx>,
    renaming: &RefCell<Renaming>,
    names: &N,
) -> Contract {
    let requires = pre.requires.into_iter().map(|cond| lower_condition(ctx, names, cond)).collect();
    renaming.borrow_mut().open_scope();
    renaming.borrow_mut().bound(Symbol::intern("result"), "result");
    let ensures = pre.ensures.into_iter().map(|cond| lower_condition(ctx, names, cond)).collect();
    renaming.borrow_mut().close_scope();
    let variant = pre.variant.map(|term| lower_pure(ctx, names, &term));
    Contract { requires, ensures, variant }
}
