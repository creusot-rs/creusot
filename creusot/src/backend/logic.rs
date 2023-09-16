use std::borrow::Cow;

use crate::{
    backend::{all_generic_decls_for, closure_generic_decls},
    ctx::*,
    util,
    util::get_builtin,
};
use rustc_hir::def_id::DefId;
use why3::{
    declaration::*,
    exp::{BinOp, Binder, Exp},
    Ident, QName,
};

use super::{
    signature::signature_of,
    term::{lower_impure, lower_pure},
    CloneSummary, Why3Generator,
};

pub(crate) fn binders_to_args(
    ctx: &mut Why3Generator,
    binders: Vec<Binder>,
) -> (Vec<why3::Exp>, Vec<Binder>) {
    let mut args = Vec::new();
    let mut out_binders = Vec::new();
    let mut fresh = 0;
    for b in binders {
        match b {
            Binder::Wild => {
                args.push(Exp::pure_var(format!("_wild{fresh}").into()));
                out_binders.push(Binder::Named(format!("_wild{fresh}").into()));
                fresh += 1;
            }
            Binder::UnNamed(_) => unreachable!("unnamed parameter in logical function signature"),
            Binder::Named(ref nm) => {
                args.push(Exp::pure_var(nm.clone()));
                out_binders.push(b);
            }
            Binder::Typed(ghost, binders, ty) => {
                let (inner_args, inner_binders) = binders_to_args(ctx, binders);
                args.extend(inner_args);
                out_binders.push(Binder::Typed(ghost, inner_binders, ty));
            }
        }
    }
    (args, out_binders)
}

pub(crate) fn translate_logic_or_predicate<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (Module, Module, Option<Module>, bool, CloneSummary<'tcx>) {
    let has_axioms = !ctx.sig(def_id).contract.is_empty();

    let (body_modl, deps) = if get_builtin(ctx.tcx, def_id).is_some() {
        builtin_body(ctx, def_id)
    } else {
        body_module(ctx, def_id)
    };
    let proof_modl = if def_id.is_local() { proof_module(ctx, def_id) } else { None };
    (stub_module(ctx, def_id), body_modl, proof_modl, has_axioms, deps)
}

fn builtin_body<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id.into(), CloneLevel::Stub);
    let mut sig = signature_of(ctx, &mut names, def_id);
    let (val_args, val_binders) = binders_to_args(ctx, sig.args);
    sig.args = val_binders;

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if !sig.contract.is_empty() {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    // Program symbol (for proofs)
    let mut val_sig = sig.clone();
    val_sig.contract.ensures = vec![Exp::pure_var("result".into())
        .eq(Exp::pure_var(val_sig.name.clone()).app(val_args.clone()))];

    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }

    let builtin = QName::from_string(get_builtin(ctx.tcx, def_id).unwrap().as_str()).unwrap();

    if !builtin.module.is_empty() {
        names.import_builtin_module(builtin.clone().module_qname());
    }

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    let (clones, summary) = names.to_clones(ctx);

    decls.extend(clones);
    if !builtin.module.is_empty() {
        let body = Exp::pure_qvar(builtin.without_search_path()).app(val_args);

        if util::is_predicate(ctx.tcx, def_id) {
            decls.push(Decl::PredDecl(Predicate { sig, body }));
        } else {
            decls.push(Decl::LogicDefn(Logic { sig, body }));
        }
    }

    decls.push(Decl::ValDecl(ValDecl { ghost: false, val: true, kind: None, sig: val_sig }));

    let name = module_name(ctx.tcx, def_id);

    (Module { name, decls }, summary)
}

// Create the program symbol with the same name that has a contract agreeing with the logical symbol.
pub(crate) fn val_decl<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut CloneMap<'tcx>,
    def_id: DefId,
) -> Decl {
    let mut sig = signature_of(ctx, names, def_id);
    sig.contract.variant = Vec::new();

    let (val_args, val_binders) = binders_to_args(ctx, sig.args);
    sig.contract
        .ensures
        // = vec!(Exp::pure_var("result".into()).eq(Exp::pure_var(sig.name.clone()).app(val_args)));
        .push(Exp::pure_var("result".into()).eq(Exp::pure_var(sig.name.clone()).app(val_args)));
    sig.args = val_binders;
    Decl::ValDecl(ValDecl { sig, ghost: false, val: true, kind: None })
}

fn body_module<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id.into(), CloneLevel::Stub);

    let mut sig = signature_of(ctx, &mut names, def_id);
    let mut val_sig = sig.clone();
    val_sig.contract.variant = Vec::new();
    let (val_args, val_binders) = binders_to_args(ctx, val_sig.args);
    val_sig.contract.ensures =
        vec![Exp::pure_var("result".into()).eq(Exp::pure_var(sig.name.clone()).app(val_args))];
    val_sig.args = val_binders;

    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }

    let sig_contract = sig.clone();
    sig.contract = Contract::new();

    let mut decls: Vec<_> = Vec::new();

    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
        decls.push(Decl::ValDecl(val));
        decls.push(val_decl(ctx, &mut names, def_id));
    } else {
        let term = ctx.term(def_id).unwrap().clone();
        let body = lower_pure(ctx, &mut names, term);

        if sig_contract.contract.variant.is_empty() {
            let decl = match util::item_type(ctx.tcx, def_id) {
                ItemType::Ghost | ItemType::Logic => Decl::LogicDefn(Logic { sig, body }),
                ItemType::Predicate => Decl::PredDecl(Predicate { sig, body }),
                _ => unreachable!(),
            };
            decls.push(decl);
            decls.push(val_decl(ctx, &mut names, def_id));
        } else if body.is_pure() {
            let def_sig = sig.clone();
            let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
            decls.push(Decl::ValDecl(val));
            decls.push(val_decl(ctx, &mut names, def_id));
            decls.push(Decl::Axiom(definition_axiom(&def_sig, body)));
        } else {
            let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
            decls.push(Decl::ValDecl(val));
            decls.push(val_decl(ctx, &mut names, def_id));
        }
    }

    let has_axioms = !ctx.sig(def_id).contract.ensures.is_empty();
    if has_axioms {
        decls.push(Decl::Axiom(spec_axiom(&sig_contract)));
    }

    let name = module_name(ctx.tcx, def_id);

    let (clones, summary) = names.to_clones(ctx);
    let decls = closure_generic_decls(ctx.tcx, def_id)
        .chain(clones.into_iter())
        .chain(decls.into_iter())
        .collect();

    (Module { name, decls }, summary)
}

pub(crate) fn stub_module(ctx: &mut Why3Generator, def_id: DefId) -> Module {
    let mut names = CloneMap::new(ctx.tcx, def_id.into(), CloneLevel::Stub);
    let mut sig = signature_of(ctx, &mut names, def_id);

    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }
    sig.contract = Contract::new();

    let decl = Decl::ValDecl(util::item_type(ctx.tcx, def_id).val(sig));

    let name = module_name(ctx.tcx, def_id);
    let name = format!("{}_Stub", &*name).into();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    let (clones, _) = names.to_clones(ctx);
    decls.extend(clones);
    decls.push(decl);

    Module { name, decls }
}

fn proof_module(ctx: &mut Why3Generator, def_id: DefId) -> Option<Module> {
    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        return None;
    }

    let mut names = CloneMap::new(ctx.tcx, def_id.into(), CloneLevel::Body);

    let mut sig = signature_of(ctx, &mut names, def_id);

    if sig.contract.is_empty() {
        let _ = names.to_clones(ctx);
        return None;
    }
    let term = ctx.term(def_id).unwrap().clone();
    let body = lower_impure(ctx, &mut names, term);

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    let (clones, _) = names.to_clones(ctx);
    decls.extend(clones);

    let kind = match util::item_type(ctx.tcx, def_id) {
        ItemType::Predicate => {
            sig.retty = None;
            Some(LetKind::Predicate)
        }
        ItemType::Ghost | ItemType::Logic => Some(LetKind::Function),
        _ => unreachable!(),
    };

    decls.push(Decl::Let(LetDecl { sig, rec: true, ghost: true, body, kind }));

    let name = impl_name(ctx, def_id);
    Some(Module { name, decls })
}

pub(crate) fn spec_axiom(sig: &Signature) -> Axiom {
    let mut ensures = sig.contract.ensures.clone();
    let postcondition: Exp = ensures.pop().unwrap_or(Exp::mk_true());

    let mut postcondition = ensures.into_iter().rfold(postcondition, Exp::lazy_conj);
    postcondition.reassociate();

    let preconditions = sig.contract.requires.iter().cloned();
    let mut condition = preconditions.rfold(postcondition, |acc, arg| arg.implies(acc));

    let func_call = function_call(sig);
    condition.subst(&[("result".into(), func_call)].into_iter().collect());
    let args: Vec<(_, _)> = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .collect();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, Box::new(condition)) };

    Axiom { name: format!("{}_spec", &*sig.name).into(), rewrite: false, axiom }
}

fn function_call(sig: &Signature) -> Exp {
    let mut args: Vec<_> = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .map(|arg| Exp::pure_var(arg.0))
        .collect();
    if args.is_empty() {
        args = vec![Exp::Tuple(vec![])];
    }

    Exp::pure_var(sig.name.clone()).app(args)
}

fn definition_axiom(sig: &Signature, body: Exp) -> Axiom {
    let call = function_call(sig);

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call), Box::new(body));

    let preconditions = sig.contract.requires.iter().cloned();
    let condition = preconditions.rfold(equation, |acc, arg| arg.implies(acc));

    let args: Vec<_> = sig.args.clone().into_iter().flat_map(|b| b.var_type_pairs()).collect();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, Box::new(condition)) };

    Axiom { name: "def".into(), rewrite: false, axiom }
}

pub(crate) fn impl_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    format!("{}_Impl", Cow::from(&*module_name(ctx.tcx, def_id))).into()
}
