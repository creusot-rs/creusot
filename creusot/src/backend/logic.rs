use crate::{
    backend::{
        Why3Generator, common_meta_decls, is_trusted_item, logic::vcgen::wp,
        signature::lower_logic_sig, term::lower_pure, ty::translate_ty,
    },
    contracts_items::get_builtin,
    ctx::*,
    naming::name,
    translated_item::FileModule,
    translation::pearlite::Term,
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident,
    declaration::*,
    exp::{BinOp, Exp, Trigger},
};

mod vcgen;

pub(crate) fn translate_logic(ctx: &Why3Generator, def_id: DefId) -> Option<FileModule> {
    let mut names = Dependencies::new(ctx, def_id);
    let pre_sig = ctx.sig(def_id).clone().normalize(ctx.tcx, ctx.typing_env(def_id));

    if pre_sig.contract.is_empty() {
        return None;
    }

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if get_builtin(ctx.tcx, def_id).is_some() {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    if !def_id.is_local() || is_trusted_item(ctx.tcx, def_id) || !ctx.has_body(def_id) {
        return None;
    }

    let mut body_decls = Vec::new();

    let args = pre_sig.inputs.clone();
    let bound: Box<[Ident]> = args.iter().map(|(name, _, _)| name.0).collect();

    let name = names.item_ident(names.self_id, names.self_subst);
    let sig = lower_logic_sig(ctx, &mut names, name, pre_sig, def_id);
    let (param_decls, args_names): (Vec<_>, Vec<_>) = args
        .into_iter()
        .map(|(name, span, ty)| {
            let name = name.0;
            let decl = Decl::LogicDecl(LogicDecl {
                kind: Some(DeclKind::Constant),
                sig: Signature {
                    name,
                    trigger: None,
                    attrs: vec![],
                    retty: Some(translate_ty(ctx, &names, span, ty)),
                    args: Box::new([]),
                    contract: Default::default(),
                },
            });
            (decl, name)
        })
        .unzip();
    body_decls.extend(param_decls);

    let val_decl = {
        let mut sig = sig.clone();
        sig.contract = Default::default();
        match ctx.item_type(def_id) {
            ItemType::Logic { .. } => {
                let kind = if sig.retty == None {
                    Some(DeclKind::Predicate)
                } else {
                    Some(DeclKind::Function)
                };
                LogicDecl { sig, kind }
            }
            ItemType::Program | ItemType::Closure => LogicDecl { sig, kind: None },
            ItemType::Constant => LogicDecl { sig, kind: Some(DeclKind::Constant) },
            _ => unreachable!(),
        }
    };
    body_decls.push(Decl::LogicDecl(val_decl));

    let postcondition = sig.contract.ensures_conj_labelled();

    let term = ctx.ctx.term(def_id).unwrap().rename(&bound);
    let wp = wp(
        ctx,
        &mut names,
        def_id,
        args_names,
        sig.contract.variant.clone(),
        term,
        name::result(),
        postcondition.clone(),
    )
    .unwrap_or_else(|e| ctx.fatal_error(e.span(), &format!("translate_logic: {e:?}")).emit());

    let goal = sig.contract.requires_implies(wp);

    let vc_ident = sig.name.refresh_with(|s| format!("vc_{s}"));
    body_decls.push(Decl::Goal(Goal { name: vc_ident, goal }));

    let mut decls = names.provide_deps(ctx);
    decls.extend(common_meta_decls());
    decls.extend(body_decls);

    let attrs = ctx.span_attr(ctx.def_span(def_id)).into_iter().collect();
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Some(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
}

/// Translate a logical term to why3.
pub(crate) fn lower_logical_defn<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    sig: Signature,
    kind: DeclKind,
    body: Term<'tcx>,
) -> Vec<Decl> {
    let mut decls = vec![];

    let body = lower_pure(ctx, names, &body);
    let lim_name = if sig.uses_simple_triggers() {
        Some(sig.name.refresh_with(|s| format!("{s}_lim")))
    } else {
        None
    };

    if sig.contract.variant.is_none() {
        let mut sig = sig.clone();
        sig.contract = Default::default();

        let decl = match kind {
            DeclKind::Function => Decl::LogicDefn(LogicDefn { sig, body }),
            DeclKind::Predicate => Decl::PredDecl(Predicate { sig, body }),
            DeclKind::Constant => Decl::ConstantDecl(Constant {
                name: sig.name,
                type_: sig.retty.unwrap(),
                body: Some(body),
            }),
        };

        decls.push(decl)
    } else {
        let mut decl_sig = sig.clone();
        decl_sig.contract = Default::default();

        decls.push(Decl::LogicDecl(LogicDecl { kind: Some(kind), sig: decl_sig }));

        if let Some(lim_name) = lim_name {
            limited_function_encode(&mut decls, &sig, lim_name, body, kind)
        } else {
            decls.push(Decl::Axiom(definition_axiom(&sig, body, "def")));
        }
    }

    if !sig.contract.ensures.is_empty() {
        if let Some(lim_name) = lim_name
            && !sig.contract.variant.is_none()
        {
            let mut lim_sig = sig;
            lim_sig.name = lim_name;
            lim_sig.trigger = Some(Trigger::single(function_call(&lim_sig)));
            lim_sig.attrs = vec![];

            decls.extend(spec_axioms(&lim_sig))
        } else {
            decls.extend(spec_axioms(&sig));
        }
    }

    decls
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
    lim_name: Ident,
    body: Exp,
    kind: DeclKind,
) {
    let mut lim_sig = Signature {
        name: lim_name,
        trigger: None,
        attrs: vec![],
        retty: sig.retty.clone(),
        args: sig.args.clone(),
        contract: Default::default(),
    };
    let lim_call = function_call(&lim_sig);
    lim_sig.trigger = Some(Trigger::single(lim_call.clone()));
    decls.push(Decl::LogicDecl(LogicDecl { kind: Some(kind), sig: lim_sig }));
    decls.push(Decl::Axiom(definition_axiom(sig, body, "def")));
    decls.push(Decl::Axiom(definition_axiom(sig, lim_call, "def_lim")));
}

pub(crate) fn spec_axioms(sig: &Signature) -> impl Iterator<Item = Decl> {
    sig.contract.ensures.iter().map(|post| {
        let mut condition = sig.contract.requires_implies(post.exp.clone());
        condition.subst(&[(name::result(), function_call(sig).clone())].into_iter().collect());
        let axiom = Exp::forall_trig(sig.args.clone(), sig.trigger.clone(), condition);
        let name = sig.name.refresh_with(|s| format!("{s}_spec"));
        Decl::Axiom(Axiom { name, rewrite: false, axiom })
    })
}

pub fn function_call(sig: &Signature) -> Exp {
    let args = sig.args.iter().map(|(arg, _)| Exp::var(*arg));
    Exp::var(sig.name).app(args)
}

fn definition_axiom(sig: &Signature, body: Exp, suffix: &str) -> Axiom {
    let call = function_call(sig);
    let trigger = sig.trigger.clone();

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call.clone()), Box::new(body));
    let condition = sig.contract.requires_implies(equation);
    let axiom = Exp::forall_trig(sig.args.clone(), trigger, condition);

    let name = sig.name.refresh_with(|s| format!("{s}_{suffix}"));
    Axiom { name, rewrite: false, axiom }
}
