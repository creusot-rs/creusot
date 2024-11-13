use crate::{
    contracts_items::get_builtin, ctx::*, translated_item::FileModule, translation::pearlite::Term,
};
use rustc_hir::def_id::DefId;
use why3::{
    declaration::*,
    exp::{super_visit_mut, BinOp, Binder, Exp, ExpMutVisitor, Trigger},
    Ident,
};

mod vcgen;

use self::vcgen::vc;

use super::{is_trusted_function, signature::signature_of, term::lower_pure, Why3Generator};

pub(crate) fn binders_to_args(
    ctx: &mut Why3Generator,
    binders: Vec<Binder>,
) -> (Vec<Ident>, Vec<Binder>) {
    let mut args = Vec::new();
    let mut out_binders = Vec::new();
    let mut fresh = 0;
    for b in binders {
        match b {
            Binder::Wild => {
                args.push(format!("_wild{fresh}").into());
                out_binders.push(Binder::Named(format!("_wild{fresh}").into()));
                fresh += 1;
            }
            Binder::UnNamed(_) => unreachable!("unnamed parameter in logical function signature"),
            Binder::Named(ref nm) => {
                args.push(nm.clone().into());
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
) -> Option<FileModule> {
    let mut names = Dependencies::new(ctx, def_id);

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if get_builtin(ctx.tcx, def_id).is_some() {
        if signature_of(ctx, &mut names, "".into(), def_id).contract.is_empty() {
            return None;
        }

        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    let name = names.value(names.self_id, names.self_subst).as_ident();
    let mut sig = signature_of(ctx, &mut names, name, def_id);

    if sig.contract.is_empty()
        || !def_id.is_local()
        || is_trusted_function(ctx.tcx, def_id)
        || !ctx.has_body(def_id)
    {
        return None;
    }

    let term = ctx.ctx.term(def_id).unwrap().clone();

    let mut body_decls = Vec::new();

    let (arg_names, new_binders) = binders_to_args(ctx, sig.args);

    let param_decls = arg_names.iter().zip(new_binders.iter()).map(|(nm, binder)| {
        Decl::LogicDecl(LogicDecl {
            kind: Some(DeclKind::Constant),
            sig: Signature {
                name: nm.clone(),
                trigger: None,
                attrs: Vec::new(),
                retty: binder.type_of().cloned(),
                args: Vec::new(),
                contract: Default::default(),
            },
        })
    });
    body_decls.extend(param_decls);
    sig.args = new_binders;

    let mut val_sig = sig.clone();
    val_sig.contract = Default::default();
    let val_decl = match ctx.item_type(def_id) {
        ItemType::Logic { .. } => LogicDecl { sig: val_sig, kind: Some(DeclKind::Function) },
        ItemType::Predicate { .. } => {
            val_sig.retty = None;
            LogicDecl { sig: val_sig, kind: Some(DeclKind::Predicate) }
        }
        ItemType::Program | ItemType::Closure => LogicDecl { sig: val_sig, kind: None },
        ItemType::Constant => LogicDecl { sig: val_sig, kind: Some(DeclKind::Constant) },
        _ => unreachable!(),
    };
    body_decls.push(Decl::LogicDecl(val_decl));

    let postcondition = sig.contract.ensures_conj();
    let body = vc(ctx, &mut names, def_id, term, "result".into(), postcondition.clone());

    let body = match body {
        Ok(body) => body,
        Err(e) => ctx.fatal_error(e.span(), &format!("{e:?}")).emit(),
    };

    let requires = sig.contract.requires.into_iter().map(Condition::unlabelled_exp);
    let body = requires.fold(body, |acc, pre| pre.implies(acc));

    body_decls
        .extend([Decl::Goal(Goal { name: format!("vc_{}", (&*sig.name)).into(), goal: body })]);

    let mut decls = names.provide_deps(ctx);
    decls.extend(body_decls);

    let attrs = Vec::from_iter(ctx.span_attr(ctx.def_span(def_id)));
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Some(FileModule { path, modl: Module { name, decls, attrs, meta } })
}

pub(crate) fn lower_logical_defn<'tcx, N: Namer<'tcx>>(
    ctx: &mut Why3Generator<'tcx>,
    names: &mut N,
    mut sig: Signature,
    kind: Option<DeclKind>,
    body: Term<'tcx>,
) -> Vec<Decl> {
    let has_axioms = !sig.contract.ensures.is_empty();

    let sig_contract = sig.clone();

    sig.contract = Default::default();
    if let Some(DeclKind::Predicate) = kind {
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

    if has_axioms {
        if sig.uses_simple_triggers() && !sig_contract.contract.variant.is_empty() {
            let lim_name = Ident::from_string(format!("{}_lim", &*sig.name));
            let mut lim_sig = sig_contract;
            lim_sig.name = lim_name;
            lim_sig.trigger = Some(Trigger::single(function_call(&lim_sig)));
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
    kind: Option<DeclKind>,
    needs_variant: bool,
    body: Term<'tcx>,
) -> Vec<Decl> {
    if let Some(DeclKind::Predicate) = kind {
        sig.retty = None;
    }

    let body = lower_pure(ctx, names, &body);

    if !needs_variant {
        let decl = match kind {
            Some(DeclKind::Function) => Decl::LogicDefn(LogicDefn { sig, body }),
            Some(DeclKind::Predicate) => Decl::PredDecl(Predicate { sig, body }),
            Some(DeclKind::Constant) => Decl::ConstantDecl(Constant {
                name: sig.name,
                type_: sig.retty.unwrap(),
                body: Some(body),
            }),
            _ => unreachable!("{kind:?}"),
        };

        return vec![decl];
    } else {
        let def_sig = sig.clone();
        let val = LogicDecl { kind, sig };

        let mut decls = Vec::new();
        decls.push(Decl::LogicDecl(val));
        if def_sig.uses_simple_triggers() {
            limited_function_encode(&mut decls, &def_sig, body, kind)
        } else {
            decls.push(Decl::Axiom(definition_axiom(&def_sig, body, "def")));
        }
        return decls;
    }
}

fn subst_qname(body: &mut Exp, name: &Ident, lim_name: &Ident) {
    struct QNameSubst<'a>(&'a Ident, &'a Ident);

    impl<'a> ExpMutVisitor for QNameSubst<'a> {
        fn visit_mut(&mut self, exp: &mut Exp) {
            match exp {
                Exp::QVar(qname) if qname.is_ident(self.0) => *exp = Exp::var(self.1.clone()),
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
    kind: Option<DeclKind>,
) {
    let lim_name = Ident::from_string(format!("{}_lim", &*sig.name));
    subst_qname(&mut body, &sig.name, &lim_name);
    let mut lim_sig = Signature {
        name: lim_name,
        trigger: None,
        attrs: vec![],
        retty: sig.retty.clone(),
        args: sig.args.clone(),
        contract: sig.contract.clone(),
    };
    let lim_call = function_call(&lim_sig);
    lim_sig.trigger = Some(Trigger::single(lim_call.clone()));
    decls.push(Decl::LogicDecl(LogicDecl { kind, sig: lim_sig }));
    decls.push(Decl::Axiom(definition_axiom(&sig, body, "def")));
    decls.push(Decl::Axiom(definition_axiom(&sig, lim_call, "def_lim")));
}

pub(crate) fn spec_axiom(sig: &Signature) -> Axiom {
    let postcondition = sig.contract.ensures_conj();
    let mut condition = sig.contract.requires_implies(postcondition);

    let func_call = function_call(sig);
    let trigger = sig.trigger.clone().into_iter().collect();
    condition.subst(&mut [("result".into(), func_call.clone())].into_iter().collect());
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

pub fn function_call(sig: &Signature) -> Exp {
    let mut args: Vec<_> = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .map(|arg| Exp::var(arg.0))
        .collect();
    if args.is_empty() {
        args = vec![Exp::Tuple(vec![])];
    }

    Exp::var(sig.name.clone()).app(args)
}

fn definition_axiom(sig: &Signature, body: Exp, suffix: &str) -> Axiom {
    let call = function_call(sig);
    let trigger = sig.trigger.clone().into_iter().collect();

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call.clone()), Box::new(body));
    let condition = sig.contract.requires_implies(equation);

    let args: Vec<_> = sig.args.clone().into_iter().flat_map(|b| b.var_type_pairs()).collect();

    let axiom =
        if args.is_empty() { condition } else { Exp::forall_trig(args, trigger, condition) };

    let name = format!("{}_{suffix}", &*sig.name);
    Axiom { name: name.into(), rewrite: false, axiom }
}
