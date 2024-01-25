use std::borrow::Cow;

use crate::{
    backend::all_generic_decls_for, ctx::*, translation::pearlite::Term, util, util::get_builtin,
};
use rustc_hir::def_id::DefId;
use why3::{
    declaration::*,
    exp::{super_visit_mut, BinOp, Binder, Exp, ExpMutVisitor, Trigger},
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
) -> (Option<Module>, CloneSummary<'tcx>) {
    let deps = if get_builtin(ctx.tcx, def_id).is_some() {
        builtin_body(ctx, def_id).1
    } else {
        body_deps(ctx, def_id)
    };

    let proof_modl = if def_id.is_local() { proof_module(ctx, def_id) } else { None };
    (proof_modl, deps)
}

fn builtin_body<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
) -> (Module, CloneSummary<'tcx>) {
    let mut names = CloneMap::new(ctx.tcx, def_id.into());
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
        // names.import_builtin_module(builtin.clone().module_qname());
    }

    let mut decls: Vec<_> = all_generic_decls_for(ctx.tcx, def_id).collect();
    let (clones, summary) = names.to_clones(ctx, CloneDepth::Shallow);

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
pub(crate) fn val_decl<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
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

fn body_decls<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    def_id: DefId,
) -> Vec<Decl> {
    let mut decls: Vec<_> = Vec::new();

    // let (mut sig, val_sig) = sigs(ctx, sig);
    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        let mut sig = signature_of(ctx, names, def_id);
        sig.contract.variant = Vec::new();

        let val = util::item_type(ctx.tcx, def_id).val(sig);
        decls.push(Decl::ValDecl(val));
        decls.push(val_decl(ctx, names, def_id));
        return decls;
    }

    let term = ctx.term(def_id).unwrap().clone();

    let sig = signature_of(ctx, names, def_id);

    lower_logical_defn(ctx, names, sig, util::item_type(ctx.tcx, def_id).let_kind(), term)
}

pub(crate) fn lower_logical_defn<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    sig: Signature,
    kind: Option<LetKind>,
    body: Term<'tcx>,
) -> Vec<Decl> {
    let has_axioms = !sig.contract.ensures.is_empty();

    let sig_contract = sig.clone();
    let (mut sig, val_sig) = sigs(ctx, sig);
    if let Some(LetKind::Predicate) = kind {
        sig.retty = None;
    }

    let mut decls = lower_pure_defn(
        ctx,
        names,
        sig.clone(),
        kind,
        !sig_contract.contract.variant.is_empty(),
        body,
    );

    decls.push(Decl::val(val_sig));

    if has_axioms {
        if sig.uses_simple_triggers() {
            let lim_name = Ident::from_string(format!("{}_lim", &*sig.name));
            let mut lim_sig = sig.clone();
            lim_sig.name = lim_name;
            lim_sig.trigger = None;
            lim_sig.attrs = vec![];

            let lim_spec = spec_axiom(&lim_sig);
            decls.push(Decl::Axiom(lim_spec))
        } else {
            decls.push(Decl::Axiom(spec_axiom(&sig_contract)));
        }
    }

    decls
}

pub(crate) fn lower_pure_defn<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    mut sig: Signature,
    kind: Option<LetKind>,
    needs_variant: bool,
    body: Term<'tcx>,
) -> Vec<Decl> {
    if let Some(LetKind::Predicate) = kind {
        sig.retty = None;
    }

    let body = lower_pure(ctx, names, &body);

    if !body.is_pure() {
        let val = ValDecl { ghost: false, val: false, kind, sig };
        return vec![Decl::ValDecl(val)];
    }

    if !needs_variant {
        let decl = match kind {
            Some(LetKind::Function) => Decl::LogicDefn(Logic { sig, body }),
            Some(LetKind::Predicate) => Decl::PredDecl(Predicate { sig, body }),
            _ => unreachable!("{kind:?}"),
        };

        return vec![decl];
    } else {
        let def_sig = sig.clone();
        let val = ValDecl { ghost: false, val: false, kind, sig };

        let mut decls = Vec::new();
        decls.push(Decl::ValDecl(val));
        if def_sig.uses_simple_triggers() {
            limited_function_encode(&mut decls, &def_sig, body, kind)
        } else {
            decls.push(Decl::Axiom(definition_axiom(&def_sig, body, "def")));
        }
        return decls;
    }
}

pub fn sigs<'tcx>(ctx: &mut Why3Generator<'tcx>, mut sig: Signature) -> (Signature, Signature) {
    let mut contract = std::mem::take(&mut sig.contract);
    let mut prog_sig = sig.clone();

    contract.variant = Vec::new();
    prog_sig.contract = contract;
    let (val_args, val_binders) = binders_to_args(ctx, prog_sig.args);
    prog_sig.args = val_binders;

    prog_sig.contract.ensures =
        vec![Exp::pure_var("result".into()).eq(Exp::pure_var(sig.name.clone()).app(val_args))];

    (sig, prog_sig)
}

fn body_deps<'tcx>(ctx: &mut Why3Generator<'tcx>, def_id: DefId) -> CloneSummary<'tcx> {
    let mut names = CloneMap::new(ctx.tcx, def_id.into());

    let _ = body_decls(ctx, &mut names, def_id);

    let (_, summary) = names.to_clones(ctx, CloneDepth::Shallow);

    summary
}

fn subst_qname(body: &mut Exp, name: &Ident, lim_name: &Ident) {
    struct QNameSubst<'a>(&'a Ident, &'a Ident);

    impl<'a> ExpMutVisitor for QNameSubst<'a> {
        fn visit_mut(&mut self, exp: &mut Exp) {
            match exp {
                Exp::QVar(qname, _) if qname.module.is_empty() && &qname.name == self.0 => {
                    *exp = Exp::pure_var(self.1.clone())
                }
                _ => super_visit_mut(self, exp),
            }
        }
    }

    QNameSubst(name, lim_name).visit_mut(body)
}

// Use the limited function encoding from https://pm.inf.ethz.ch/publications/HeuleKassiosMuellerSummers12.pdf
// Originally introduced in https://dl.acm.org/doi/10.1145/1529282.1529411

// This prevents recursive functions from being unfolded more than once which makes the definition
// axiom weaker but avoids having it cause a matching loop. This is useful since it can help the
// solve return "unknown" instead of relying on a timeout, and give it a chance to apply map
// extensionality axioms.
fn limited_function_encode(
    decls: &mut Vec<Decl>,
    sig: &Signature,
    mut body: Exp,
    kind: Option<LetKind>,
) {
    let lim_name = Ident::from_string(format!("{}_lim", &*sig.name));
    subst_qname(&mut body, &sig.name, &lim_name);
    let lim_sig = Signature {
        name: lim_name,
        trigger: None,
        attrs: vec![],
        retty: sig.retty.clone(),
        args: sig.args.clone(),
        contract: sig.contract.clone(),
    };
    let lim_call = function_call(&lim_sig);
    decls.push(Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig: sig.clone() }));
    decls.push(Decl::Axiom(definition_axiom(&sig, body, "def")));
    decls.push(Decl::Axiom(definition_axiom(&sig, lim_call, "def_lim")));
}

fn proof_module(ctx: &mut Why3Generator, def_id: DefId) -> Option<Module> {
    if util::is_trusted(ctx.tcx, def_id) || !util::has_body(ctx, def_id) {
        return None;
    }

    let mut names = CloneMap::new(ctx.tcx, def_id.into());

    let mut sig = signature_of(ctx, &mut names, def_id);

    if sig.contract.is_empty() {
        let _ = names.to_clones(ctx, CloneDepth::Deep);
        return None;
    }
    let term = ctx.term(def_id).unwrap().clone();
    let body = lower_impure(ctx, &mut names, &term);

    let mut decls: Vec<_> = Vec::new();
    decls.extend(all_generic_decls_for(ctx.tcx, def_id));
    let (clones, _) = names.to_clones(ctx, CloneDepth::Deep);
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
    let trigger = sig.trigger.clone().unwrap_or_else(|| Trigger::single(func_call.clone()));
    condition.subst(&[("result".into(), func_call.clone())].into_iter().collect());
    let args: Vec<(_, _)> = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .collect();

    let axiom =
        if args.is_empty() { condition } else { Exp::forall_trig(args, trigger, condition) };

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

fn definition_axiom(sig: &Signature, body: Exp, suffix: &str) -> Axiom {
    let call = function_call(sig);
    let trigger = sig.trigger.clone().unwrap_or_else(|| Trigger::single(call.clone()));

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call.clone()), Box::new(body));

    let preconditions = sig.contract.requires.iter().cloned();
    let condition = preconditions.rfold(equation, |acc, arg| arg.implies(acc));

    let args: Vec<_> = sig.args.clone().into_iter().flat_map(|b| b.var_type_pairs()).collect();

    let axiom =
        if args.is_empty() { condition } else { Exp::forall_trig(args, trigger, condition) };

    let name = format!("{}_{suffix}", &*sig.name);
    Axiom { name: name.into(), rewrite: false, axiom }
}

pub(crate) fn impl_name(ctx: &TranslationCtx, def_id: DefId) -> Ident {
    format!("{}_Impl", Cow::from(&*module_name(ctx.tcx, def_id))).into()
}
