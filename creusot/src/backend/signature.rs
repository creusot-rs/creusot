use std::collections::HashMap;

use crate::{
    backend::{
        DefKind, Why3Generator,
        clone_map::Namer,
        term::{lower_condition, lower_pure, lower_trigger},
        ty::translate_ty,
    },
    contracts_items::why3_attrs,
    naming::name,
    translation::specification::{PreContract, PreSignature},
};
use rustc_hir::def_id::DefId;
use why3::{
    Exp, Ident,
    coma::{Param, Prototype},
    declaration::{Attribute, Condition, Signature},
    exp::Trigger,
};

#[derive(Debug, Clone)]
pub(crate) struct Contract {
    pub(crate) requires: Box<[Condition]>,
    pub(crate) ensures: Box<[(Box<[Trigger]>, Condition)]>,
}

impl Contract {
    // Don't add `stop_split` if there's already one.
    fn add_stop_split(exp: Exp, name: &str, kind: &str) -> Exp {
        if let Exp::Attr(Attribute::Attr(a1), box Exp::Attr(Attribute::Attr(a2), _)) = &exp
            && a1 == "stop_split"
            && a2.starts_with("expl:")
        {
            exp
        } else {
            exp.with_attr(Attribute::Attr(format!("expl:{name} {kind}")))
                .with_attr(Attribute::Attr("stop_split".into()))
        }
    }

    pub fn ensures_conj(&self, name: &str) -> Exp {
        let mut ensures = self.ensures.iter().cloned().map(|(_, cond)| cond.labelled_exp());
        let Some(mut postcond) = ensures.next() else { return Exp::mk_true() };
        postcond = ensures.fold(postcond, Exp::log_and);
        postcond.reassociate();
        Contract::add_stop_split(postcond, name, "ensures")
    }

    pub fn requires_conj(&self, name: &str) -> Exp {
        let mut requires = self.requires.iter().cloned().map(Condition::labelled_exp);
        let Some(mut postcond) = requires.next() else { return Exp::mk_true() };
        postcond = requires.fold(postcond, Exp::log_and);
        postcond.reassociate();
        Contract::add_stop_split(postcond, name, "requires")
    }

    pub fn requires_implies(&self, conclusion: Exp) -> Exp {
        self.requires.iter().rfold(conclusion, |acc, arg| arg.exp.clone().implies(acc))
    }

    pub fn subst(&mut self, subst: &HashMap<Ident, Exp>) {
        for req in self.requires.iter_mut() {
            req.exp.subst(subst);
        }

        for ens in self.ensures.iter_mut() {
            ens.1.exp.subst(subst);
            for t in ens.0.iter_mut().flat_map(|t| &mut t.0) {
                t.subst(subst);
            }
        }
    }
}

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
pub(crate) fn lower_program_sig<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    name: Ident,
    mut pre_sig: PreSignature<'tcx>,
    // FIXME: Get rid of this def id
    // The PreSig should have the name and the id should be replaced by a param env (if by anything at all...)
    def_id: DefId,
    return_ident: Ident,
) -> ProgramSignature {
    let span = ctx.tcx.def_span(def_id);
    let return_ty = translate_ty(ctx, names, span, pre_sig.output);
    let params: Box<[Param]> = std::iter::once(Param::Term(name::mode(), super::ty::mode(names)))
        .chain(
            pre_sig
                .inputs
                .iter()
                .map(|(id, span, ty)| Param::Term(id.0, translate_ty(ctx, names, *span, *ty))),
        )
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

    let variant = pre_sig.contract.variant.take().map(|term| {
        let ty = translate_ty(ctx, names, term.span, term.ty);
        (lower_pure(ctx, names, &term.spanned()), ty)
    });
    let contract = lower_contract(ctx, names, pre_sig.contract);

    ProgramSignature { prototype: Prototype { name, attrs, params }, contract, return_ty, variant }
}

/// The signature of a logical function
#[derive(Debug, Clone)]
pub(crate) struct LogicSignature {
    pub(crate) why_sig: Signature,
    pub(crate) contract: Contract,
    pub(crate) variant: Option<why3::Exp>,
}

/// Translates a Pearlite (logical) function signature to a whyml signature.
///
/// Note that `pre_sig` should be normalized!
pub(crate) fn lower_logic_sig<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
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

    let retty = if pre_sig.output.is_bool() {
        None
    } else {
        Some(translate_ty(ctx, names, span, pre_sig.output))
    };
    let variant =
        pre_sig.contract.variant.take().map(|term| lower_pure(ctx, names, &term.spanned()));
    let contract = lower_contract(ctx, names, pre_sig.contract);

    LogicSignature { why_sig: Signature { name, attrs, retty, args }, contract, variant }
}

pub(crate) fn lower_contract<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    contract: PreContract<'tcx>,
) -> Contract {
    let requires =
        contract.requires.into_iter().map(|cond| lower_condition(ctx, names, cond)).collect();
    let ensures = contract
        .ensures
        .into_iter()
        .map(|(trig, cond)| {
            (
                trig.into_iter().map(|t| lower_trigger(ctx, names, t)).collect(),
                lower_condition(ctx, names, cond),
            )
        })
        .collect();
    Contract { requires, ensures }
}
