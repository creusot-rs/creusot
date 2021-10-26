use crate::{
    clone_map::CloneMap,
    ctx::{translate_value_id, TranslationCtx},
    translation::function::all_generic_decls_for,
    util,
};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;
use std::borrow::Cow;
use why3::{
    declaration::{Axiom, Contract, Decl, LetDecl, Module, Signature, ValKind},
    mlcfg::{BinOp, Exp},
    name::Ident,
};

use super::specification;

pub fn translate_pure(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    _span: rustc_span::Span,
) -> (Module, Option<Module>, CloneMap<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id, false);
    names.clone_self(def_id);

    let sig = crate::util::signature_of(ctx, &mut names, def_id);

    let name = translate_value_id(ctx.tcx, def_id).module_ident().unwrap().clone();

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));

    decls.extend(names.to_clones(ctx));
    decls.extend(declaration(sig.clone()));

    let impl_mod = if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        None
    } else {
        let term = ctx.term(def_id).unwrap().clone();
        let body = specification::lower(ctx, &mut names, def_id, term);

        decls.extend(names.to_clones(ctx));

        if body.is_pure() {
            decls.push(Decl::Axiom(definition_axiom(&sig, body.clone())));
        }
        implementation_module(ctx, def_id, &names, sig, body)
    };

    (Module { name, decls }, impl_mod, names)
}

pub(crate) fn declaration(mut sig: Signature) -> impl Iterator<Item = Decl> {
    sig.contract.variant = Vec::new();

    [
        Decl::ValDecl(function_symbol(sig.clone())),
        Decl::ValDecl(program_symbol(sig.clone())),
        Decl::Axiom(spec_axiom(&sig)),
    ]
    .into_iter()
}

fn function_symbol(mut sig: Signature) -> ValKind {
    sig.contract = Contract::new();
    ValKind::Function { sig }
}

fn program_symbol(mut sig: Signature) -> ValKind {
    let call = function_call(&sig);
    sig.contract.ensures.push(Exp::BinaryOp(BinOp::Eq, box Exp::Var("result".into()), box call));
    ValKind::Val { sig }
}

fn function_call(sig: &Signature) -> Exp {
    let mut args: Vec<_> = sig.args.iter().cloned().map(|arg| Exp::Var(arg.0)).collect();
    if args.is_empty() {
        args = vec![Exp::Tuple(vec![])];
    }

    Exp::Call(box Exp::Var(sig.name.clone()), args)
}

fn spec_axiom(sig: &Signature) -> Axiom {
    let mut ensures = sig.contract.ensures.clone();
    let postcondition: Exp = ensures.pop().unwrap_or(Exp::mk_true());

    let mut postcondition = ensures.into_iter().rfold(postcondition, Exp::conj);
    postcondition.reassociate();

    let preconditions = sig.contract.requires.iter().cloned();
    let mut condition = preconditions.rfold(postcondition, |acc, arg| Exp::Impl(box arg, box acc));

    let func_call = function_call(sig);
    condition.subst(&[("result".into(), func_call)].into_iter().collect());
    let args = sig.args.clone();

    let axiom = if args.is_empty() { condition } else { Exp::Forall(args, box condition) };

    Axiom { name: format!("{}_spec", &*sig.name).into(), axiom }
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

fn implementation_module(
    ctx: &mut TranslationCtx<'_, 'tcx>,
    def_id: DefId,
    names: &CloneMap<'tcx>,
    sig: Signature,
    body: Exp,
) -> Option<Module> {
    let has_body = if let Some(local_id) = def_id.as_local() {
        let hir_id = ctx.tcx.hir().local_def_id_to_hir_id(local_id);
        if !ctx.tcx.hir().maybe_body_owned_by(hir_id).is_some() {
            false
        } else {
            true
        }
    } else {
        true
        // unreachable!()
    };
    if util::is_trusted(ctx.tcx, def_id) || !has_body {
        return None;
    }

    let mut names = names.clone();
    names.clear_graph();
    names.use_full_clones = true;

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    decls.extend(names.to_clones(ctx));
    decls.push(Decl::Let(LetDecl { sig, rec: true, body }));

    let name = impl_name(ctx.tcx, def_id);
    Some(Module { name, decls })
}

pub fn impl_name(tcx: TyCtxt, def_id: DefId) -> Ident {
    let name = translate_value_id(tcx, def_id);

    format!("{}_Impl", Cow::from(name.module_ident().unwrap())).into()
}
