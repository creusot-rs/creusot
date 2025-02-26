use std::cell::RefCell;

use crate::{
    contracts_items::get_builtin, ctx::*, translated_item::FileModule, translation::pearlite::Term,
};
use rustc_hir::def_id::DefId;
use why3::{
    declaration::*,
    exp::{super_visit_mut, BinOp, Exp, ExpMutVisitor, Trigger},
    Ident,
};

mod vcgen;

use self::vcgen::vc;

use super::{
    is_trusted_function, signature::{signature_of, PreSignature2}, term::lower_pure, CannotFetchThir, Why3Generator,
};

pub(crate) fn translate_logic_or_predicate(
    ctx: &Why3Generator,
    def_id: DefId,
) -> Result<Option<FileModule>, CannotFetchThir> {
    let mut names = Dependencies::new(ctx, def_id);

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if get_builtin(ctx.tcx, def_id).is_some() {
        let nm = Ident::bound(""); // TODO ???
        if signature_of(ctx, &mut names, nm, def_id).contract.is_empty() {
            return Ok(None);
        }

        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    let name = Ident::bound(names.item(names.self_id, names.self_subst).as_ident());
    let sig = signature_of(ctx, &mut names, name, def_id);

    if sig.contract.is_empty()
        || !def_id.is_local()
        || is_trusted_function(ctx.tcx, def_id)
        || !ctx.has_body(def_id)
    {
        return Ok(None);
    }

    let term = ctx.ctx.term(def_id)?.unwrap().clone();

    let mut body_decls = Vec::new();

    let param_decls = sig.args.iter().map(|(nm, ty)| {
        Decl::LogicDecl(LogicDecl {
            kind: Some(DeclKind::Constant),
            sig: Signature {
                name: nm.unwrap_or(Ident::bound("_tt")), // TODO: get rid of this Option?
                trigger: None,
                attrs: Vec::new(),
                retty: Some(ty.clone()),
                args: Vec::new(),
                contract: Default::default(),
            },
        })
    });
    body_decls.extend(param_decls);

    let mut val_sig = Signature::from(sig.clone());
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
    let body = vc(ctx, &mut names, def_id, term, Ident::bound("result"), postcondition.clone());

    let body = match body {
        Ok(body) => body,
        Err(e) => ctx.fatal_error(e.span(), &format!("translate_logic_or_predicate: {e:?}")).emit(),
    };

    let requires = sig.contract.requires.into_iter().map(Condition::unlabelled_exp);
    let body = requires.fold(body, |acc, pre| pre.implies(acc));

    let goal_ident = Ident::fresh(format!("vc_{}", sig.name.as_str()));
    body_decls
        .extend([Decl::Goal(Goal { name: goal_ident, goal: body })]);

    let mut decls = names.provide_deps(ctx);
    decls.extend(body_decls);

    let attrs = Vec::from_iter(ctx.span_attr(ctx.def_span(def_id)));
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Ok(Some(FileModule { path, modl: Module { name, decls, attrs, meta } }))
}

pub(crate) fn lower_logical_defn<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    mut sig: PreSignature2,
    kind: Option<DeclKind>,
    body: Term<'tcx>,
) -> Vec<Decl> {
    if let Some(DeclKind::Predicate) = kind {
        sig.retty = None;
    }

    let mut decls = vec![];

    let renaming = todo!{}; // Erase this RefCell::new(sig.args.iter().map(|(old, new, _)| (*old, *new)).collect());
    let body = lower_pure(ctx, names, &renaming, &body);

    if sig.contract.variant.is_empty() {
        let mut sig = Signature::from(sig.clone());
        sig.contract = Default::default();

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

        decls.push(decl)
    } else {
        let mut decl_sig = Signature::from(sig.clone());
        decl_sig.contract = Contract::new();
        decls.push(Decl::LogicDecl(LogicDecl { kind, sig: decl_sig }));

        if sig.uses_simple_triggers() {
            limited_function_encode(&mut decls, &sig, body, kind)
        } else {
            decls.push(Decl::Axiom(definition_axiom(&sig, body, "def")));
        }
    }

    if !sig.contract.ensures.is_empty() {
        if sig.uses_simple_triggers() && !sig.contract.variant.is_empty() {
            let lim_name = Ident::bound(format!("{}_lim", sig.name.as_str()));
            let mut lim_sig = sig;
            lim_sig.name = lim_name;
            lim_sig.trigger = Some(Trigger::single(function_call(&lim_sig)));
            lim_sig.attrs = vec![];

            let lim_spec = spec_axiom(&lim_sig);
            decls.push(Decl::Axiom(lim_spec))
        } else {
            decls.push(Decl::Axiom(spec_axiom(&sig)));
        }
    }

    decls
}

fn subst_qname(body: &mut Exp, name: &Ident, lim_name: &Ident) {
    struct QNameSubst<'a>(&'a Ident, &'a Ident);

    impl<'a> ExpMutVisitor for QNameSubst<'a> {
        fn visit_mut(&mut self, exp: &mut Exp) {
            match exp {
                Exp::QVar(qname) if qname.is_ident(&(*self.0).into()) => *exp = Exp::Var(self.1.clone()), // TODO: ???
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
    sig: &PreSignature2,
    mut body: Exp,
    kind: Option<DeclKind>,
) {
    let lim_name = Ident::fresh(format!("{}_lim", sig.name.as_str()));
    subst_qname(&mut body, &sig.name, &lim_name);
    let mut lim_sig = PreSignature2 {
        name: lim_name,
        trigger: None,
        attrs: vec![],
        retty: sig.retty.clone(),
        args: sig.args.clone(),
        contract: Contract::new(),
    };
    let lim_call = function_call(&lim_sig);
    lim_sig.trigger = Some(Trigger::single(lim_call.clone()));
    decls.push(Decl::LogicDecl(LogicDecl { kind, sig: lim_sig.into() }));
    decls.push(Decl::Axiom(definition_axiom(sig, body, "def")));
    decls.push(Decl::Axiom(definition_axiom(sig, lim_call, "def_lim")));
}

pub(crate) fn spec_axiom(sig: &PreSignature2) -> Axiom {
    let postcondition = sig.contract.ensures_conj();
    let mut condition = sig.contract.requires_implies(postcondition);

    let func_call = function_call(sig);
    let trigger = sig.trigger.clone().into_iter().collect();
    condition.subst(&mut [(Ident::bound("result"), func_call.clone())].into_iter().collect());
    let args: Vec<(_, _)> = sig
        .args
        .iter()
        .filter_map(|(name, ty)| name.map(|ident| (ident, ty.clone())))
        .collect();

    let axiom =
        if args.is_empty() { condition } else { Exp::forall_trig(args, trigger, condition) };

    Axiom { name: Ident::fresh(format!("{}_spec", sig.name.as_str())), rewrite: false, axiom }
}

pub fn function_call(sig: &PreSignature2) -> Exp {
    let mut args: Vec<_> = sig
        .args
        .iter()
        .cloned()
        .map(|arg| arg.0.map_or(Exp::unit(), Exp::Var))
        .collect();
    if args.is_empty() {
        args = vec![Exp::unit()];
    }

    Exp::Var(sig.name.clone()).app(args)
}

fn definition_axiom(sig: &PreSignature2, body: Exp, suffix: &str) -> Axiom {
    let call = function_call(sig);
    let trigger = sig.trigger.clone().into_iter().collect();

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call.clone()), Box::new(body));
    let condition = sig.contract.requires_implies(equation);
    let args: Vec<(_, _)> = sig
        .args
        .iter()
        .filter_map(|(name, ty)| name.map(|ident| (ident, ty.clone())))
        .collect();

    let axiom =
        if sig.args.is_empty() { condition } else { Exp::forall_trig(args, trigger, condition) };

    let name = Ident::fresh(format!("{}_{suffix}", sig.name.as_str()));
    Axiom { name, rewrite: false, axiom }
}
