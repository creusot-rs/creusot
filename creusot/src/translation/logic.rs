use std::borrow::Cow;

use crate::function::all_generic_decls_for;
use crate::translation::specification;
use crate::util::get_builtin;
use crate::{ctx::*, util};
use creusot_rustc::hir::def_id::DefId;
use creusot_rustc::middle::ty::TyCtxt;
use why3::declaration::*;
use why3::exp::{BinOp, Exp};
use why3::Ident;

pub fn translate_logic_or_predicate<'tcx>(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
) -> (Module, Option<Module>, bool, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, false);

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if !sig.contract.is_empty() && get_builtin(ctx.tcx, def_id).is_some() {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    def_id
        .as_local()
        .map(|d| ctx.def_span(d))
        .and_then(|span| ctx.span_attr(span))
        .map(|attr| sig.attrs.push(attr));

    let sig_contract = sig.clone();
    sig.contract = Contract::new();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    let proof_modl = proof_module(ctx, def_id);
    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        let val = util::item_type(ctx.tcx, def_id).val(sig);
        decls.push(Decl::ValDecl(val));
    } else {
        let term = ctx.term(def_id).unwrap().clone();
        let body = specification::lower_pure(ctx, &mut names, def_id, ctx.param_env(def_id), term);
        decls.extend(names.to_clones(ctx));

        if sig_contract.contract.variant.is_empty() {
            let decl = match util::item_type(ctx.tcx, def_id) {
                ItemType::Logic => Decl::LogicDecl(Logic { sig, body }),
                ItemType::Predicate => Decl::PredDecl(Predicate { sig, body }),
                _ => unreachable!(),
            };
            decls.push(decl);
        } else if body.is_pure() {
            let def_sig = sig.clone();
            let val = util::item_type(ctx.tcx, def_id).val(sig);
            decls.push(Decl::ValDecl(val));
            decls.push(Decl::Axiom(definition_axiom(&def_sig, body)));
        } else {
            let val = util::item_type(ctx.tcx, def_id).val(sig);
            decls.push(Decl::ValDecl(val));
        }
    }

    let has_axioms = !sig_contract.contract.is_empty();
    if has_axioms {
        decls.push(Decl::Axiom(spec_axiom(&sig_contract)));
    }

    let name = module_name(ctx.tcx, def_id);
    (Module { name, decls }, proof_modl, has_axioms, names)
}

fn proof_module(ctx: &mut TranslationCtx, def_id: DefId) -> Option<Module> {
    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        return None;
    }

    let mut names = CloneMap::new(ctx.tcx, def_id, true);

    let sig = crate::util::signature_of(ctx, &mut names, def_id);

    if sig.contract.is_empty() {
        let _ = names.to_clones(ctx);
        return None;
    }
    let term = ctx.term(def_id).unwrap().clone();
    let body = specification::lower_impure(ctx, &mut names, def_id, ctx.param_env(def_id), term);

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));
    decls.push(Decl::LetFun(LetFun { sig, rec: true, ghost: true, body }));

    let name = impl_name(ctx.tcx, def_id);
    Some(Module { name, decls })
}

pub(crate) fn spec_axiom(sig: &Signature) -> Axiom {
    let mut ensures = sig.contract.ensures.clone();
    let postcondition: Exp = ensures.pop().unwrap_or(Exp::mk_true());

    let mut postcondition = ensures.into_iter().rfold(postcondition, Exp::lazy_conj);
    postcondition.reassociate();

    let preconditions = sig.contract.requires.iter().cloned();
    let mut condition = preconditions.rfold(postcondition, |acc, arg| Exp::Impl(box arg, box acc));

    let func_call = function_call(sig);
    condition.subst(&[("result".into(), func_call)].into_iter().collect());
    let args: Vec<_> = sig.args.iter().cloned().filter(|arg| &*arg.0 != "_").collect();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, box condition) };

    Axiom { name: format!("{}_spec", &*sig.name).into(), axiom }
}

fn function_call(sig: &Signature) -> Exp {
    let mut args: Vec<_> = sig
        .args
        .iter()
        .cloned()
        .filter(|arg| &*arg.0 != "_")
        .map(|arg| Exp::pure_var(arg.0))
        .collect();
    if args.is_empty() {
        args = vec![Exp::Tuple(vec![])];
    }

    Exp::Call(box Exp::pure_var(sig.name.clone()), args)
}

fn definition_axiom(sig: &Signature, body: Exp) -> Axiom {
    let call = function_call(sig);

    let equation = Exp::BinaryOp(BinOp::Eq, box call, box body);

    let preconditions = sig.contract.requires.iter().cloned();
    let condition = preconditions.rfold(equation, |acc, arg| Exp::Impl(box arg, box acc));

    let args = sig.args.clone();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, box condition) };

    Axiom { name: "def".into(), axiom }
}

pub fn impl_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    format!("{}_Impl", Cow::from(&*module_name(tcx, def_id))).into()
}
