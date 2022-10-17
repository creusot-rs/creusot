use std::borrow::Cow;

use crate::{
    ctx::*,
    function::all_generic_decls_for,
    translation::specification,
    util,
    util::{get_builtin, pre_sig_of},
};
use creusot_rustc::hir::def_id::DefId;
use why3::{
    declaration::*,
    exp::{BinOp, Binder, Exp},
    Ident, QName,
};

pub(crate) fn binders_to_args(
    ctx: &mut TranslationCtx,
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
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> (Module, Module, Option<Module>, bool, CloneSummary<'tcx>) {
    let has_axioms = !pre_sig_of(ctx, def_id).contract.is_empty();

    let (body_modl, deps) = if get_builtin(ctx.tcx, def_id).is_some() {
        builtin_body(ctx, def_id)
    } else {
        body_module(ctx, def_id)
    };
    let proof_modl = if def_id.is_local() { proof_module(ctx, def_id) } else { None };
    (stub_module(ctx, def_id), body_modl, proof_modl, has_axioms, deps)
}

fn builtin_body<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Stub);
    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    let (val_args, val_binders) = binders_to_args(ctx, sig.args);
    sig.args = val_binders;

    def_id
        .as_local()
        .map(|d| ctx.def_span(d))
        .and_then(|span| ctx.span_attr(span))
        .map(|attr| sig.attrs.push(attr));

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if !sig.contract.is_empty() {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    // Program symbol (for proofs)
    let mut val_sig = sig.clone();
    val_sig.contract.ensures = vec![Exp::BinaryOp(
        BinOp::Eq,
        box Exp::pure_var("result".into()),
        box Exp::Call(box Exp::pure_var(val_sig.name.clone()), val_args.clone()),
    )];

    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }

    let builtin = QName::from_string(get_builtin(ctx.tcx, def_id).unwrap().as_str()).unwrap();

    if !builtin.module.is_empty() {
        names.import_builtin_module(builtin.clone().module_qname());
    }

    let mut decls = names.to_clones(ctx);
    if !builtin.module.is_empty() {
        let body = Exp::Call(box Exp::pure_qvar(builtin.without_search_path()), val_args);

        if util::is_predicate(ctx.tcx, def_id) {
            decls.push(Decl::PredDecl(Predicate { sig, body }));
        } else {
            decls.push(Decl::LogicDefn(Logic { sig, body }));
        }
    }

    decls.push(Decl::ValDecl(ValDecl { ghost: false, val: true, kind: None, sig: val_sig }));

    let name = module_name(ctx, def_id);

    (Module { name, decls }, names.summary())
}

fn body_module<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Stub);

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);
    let mut val_sig = sig.clone();
    val_sig.contract.variant = Vec::new();
    let (val_args, val_binders) = binders_to_args(ctx, val_sig.args);
    val_sig.contract.ensures = vec![Exp::BinaryOp(
        BinOp::Eq,
        box Exp::pure_var("result".into()),
        box Exp::Call(box Exp::pure_var(sig.name.clone()), val_args),
    )];
    val_sig.args = val_binders;

    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
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

    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
        decls.push(Decl::ValDecl(val));
        decls.push(Decl::ValDecl(ValDecl { sig: val_sig, ghost: false, val: true, kind: None }));
    } else {
        let term = ctx.term(def_id).unwrap().clone();
        let body = specification::lower_pure(ctx, &mut names, ctx.param_env(def_id), term);
        decls.extend(names.to_clones(ctx));

        if sig_contract.contract.variant.is_empty() {
            let decl = match util::item_type(ctx.tcx, def_id) {
                ItemType::Logic => Decl::LogicDefn(Logic { sig, body }),
                ItemType::Predicate => Decl::PredDecl(Predicate { sig, body }),
                _ => unreachable!(),
            };
            decls.push(decl);
            decls.push(Decl::ValDecl(ValDecl {
                sig: val_sig,
                ghost: false,
                val: true,
                kind: None,
            }));
        } else if body.is_pure() {
            let def_sig = sig.clone();
            let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
            decls.push(Decl::ValDecl(val));
            decls.push(Decl::ValDecl(ValDecl {
                sig: val_sig,
                ghost: false,
                val: true,
                kind: None,
            }));
            decls.push(Decl::Axiom(definition_axiom(&def_sig, body)));
        } else {
            let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
            decls.push(Decl::ValDecl(val));
            decls.push(Decl::ValDecl(ValDecl {
                sig: val_sig,
                ghost: false,
                val: true,
                kind: None,
            }));
        }
    }

    let has_axioms = !pre_sig_of(ctx, def_id).contract.is_empty();
    if has_axioms {
        decls.push(Decl::Axiom(spec_axiom(&sig_contract)));
    }

    let name = module_name(ctx, def_id);

    (Module { name, decls }, names.summary())
}

fn stub_module(ctx: &mut TranslationCtx, def_id: DefId) -> Module {
    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Stub);
    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);

    if util::is_predicate(ctx.tcx, def_id) {
        sig.retty = None;
    }
    sig.contract = Contract::new();

    let decl = Decl::ValDecl(util::item_type(ctx.tcx, def_id).val(sig));

    let name = module_name(ctx, def_id);
    let name = format!("{}_Stub", &*name).into();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));
    decls.push(decl);

    Module { name, decls }
}

fn proof_module(ctx: &mut TranslationCtx, def_id: DefId) -> Option<Module> {
    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        return None;
    }

    let mut names = CloneMap::new(ctx.tcx, def_id, CloneLevel::Body);

    let mut sig = crate::util::signature_of(ctx, &mut names, def_id);

    if sig.contract.is_empty() {
        let _ = names.to_clones(ctx);
        return None;
    }
    let term = ctx.term(def_id).unwrap().clone();
    let body = specification::lower_impure(ctx, &mut names, ctx.param_env(def_id), term);

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    let kind = match util::item_type(ctx.tcx, def_id) {
        ItemType::Predicate => {
            sig.retty = None;
            Some(LetKind::Predicate)
        }
        ItemType::Logic => Some(LetKind::Function),
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
    let mut condition = preconditions.rfold(postcondition, |acc, arg| Exp::Impl(box arg, box acc));

    let func_call = function_call(sig);
    condition.subst(&[("result".into(), func_call)].into_iter().collect());
    let args: Vec<(_, _)> = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .collect();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, box condition) };

    Axiom { name: format!("{}_spec", &*sig.name).into(), axiom }
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

    Exp::Call(box Exp::pure_var(sig.name.clone()), args)
}

fn definition_axiom(sig: &Signature, body: Exp) -> Axiom {
    let call = function_call(sig);

    let equation = Exp::BinaryOp(BinOp::Eq, box call, box body);

    let preconditions = sig.contract.requires.iter().cloned();
    let condition = preconditions.rfold(equation, |acc, arg| Exp::Impl(box arg, box acc));

    let args: Vec<_> = sig.args.clone().into_iter().flat_map(|b| b.var_type_pairs()).collect();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, box condition) };

    Axiom { name: "def".into(), axiom }
}

pub(crate) fn impl_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    format!("{}_Impl", Cow::from(&*module_name(ctx, def_id))).into()
}
