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
    let proof_modl = proof_module(ctx, def_id);
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
            decls.push(Decl::Let(LetDecl {
                sig,
                body,
                kind: Some(LetKind::Predicate),
                rec: true,
                ghost: true,
            }));
        } else {
            decls.push(Decl::Let(LetDecl {
                sig,
                body,
                kind: Some(LetKind::Function),
                rec: true,
                ghost: true,
            }));
        }
    }

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

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        let val = util::item_type(ctx.tcx, def_id).val(sig.clone());
        decls.push(Decl::ValDecl(val));
    } else {
        let term = ctx.term(def_id).unwrap().clone();
        let body = specification::lower_impure(ctx, &mut names, def_id, ctx.param_env(def_id), term);
        decls.extend(names.to_clones(ctx));

        // TODO: Supress proof obligations
        decls.push(Decl::Let(LetDecl {
            sig,
            rec: true,
            ghost: true,
            body,
            kind: Some(LetKind::Function),
        }));

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

    let kind = match util::item_type(ctx.tcx, def_id) {
        ItemType::Logic => LetKind::Function,
        ItemType::Predicate => LetKind::Predicate,
        _ => unreachable!(),
    };

    let decl = Decl::ValDecl(ValDecl { ghost: true, val: true, kind: Some(kind), sig });
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
    decls.push(Decl::Let(LetDecl {
        sig,
        rec: true,
        ghost: true,
        body,
        kind: Some(LetKind::Function),
    }));

    let name = impl_name(ctx, def_id);
    Some(Module { name, decls })
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

pub(crate) fn impl_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    format!("{}_Impl", Cow::from(&*module_name(ctx, def_id))).into()
}
