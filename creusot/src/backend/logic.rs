use crate::{
    backend::{
        Why3Generator, common_meta_decls, is_trusted_item,
        logic::vcgen::wp,
        signature::{LogicSignature, lower_logic_sig},
        term::lower_pure_weakdep,
        ty::{self, translate_ty},
    },
    contracts_items::get_builtin,
    ctx::*,
    naming::name,
    translated_item::FileModule,
    translation::pearlite::Term,
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident, Name,
    declaration::*,
    exp::{BinOp, Exp, Trigger},
};

mod vcgen;

pub(crate) fn translate_logic(ctx: &Why3Generator, def_id: DefId) -> Option<FileModule> {
    let names = Dependencies::new(ctx, def_id);
    let pre_sig = ctx.sig(def_id).clone().normalize(ctx, ctx.typing_env(def_id));

    let namespace_ty = names.namespace_ty();

    if pre_sig.contract.is_empty() {
        return None;
    }

    if get_builtin(ctx.tcx, def_id).is_some() {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtin` and a contract on the same definition",
        );
    }

    if !def_id.is_local() || is_trusted_item(ctx.tcx, def_id) || !ctx.has_body(def_id) {
        return None;
    }

    let mut body_decls = Vec::new();

    let args = pre_sig.inputs.clone();
    let bound: Box<[Ident]> = args.iter().map(|(name, _, _)| name.0).collect();

    let name = names.source_ident();
    let sig = lower_logic_sig(ctx, &names, name, pre_sig, def_id);
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
        let mut sig = sig.why_sig.clone();
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

    let postcondition = sig.why_sig.contract.ensures_conj_labelled();

    let term = ctx.ctx.term(def_id).unwrap().rename(&bound);
    let wp = wp(
        ctx,
        &names,
        def_id,
        args_names,
        sig.variant.clone(),
        term,
        name::result(),
        postcondition.clone(),
    );
    let goal = sig.why_sig.contract.requires_implies(wp);
    let vc_ident = sig.why_sig.name.refresh_with(|s| format!("vc_{s}"));

    let (mut decls, setters) = names.provide_deps(ctx);
    decls.extend(common_meta_decls());
    decls.extend(body_decls);
    decls.push(setters.mk_goal(vc_ident, goal));

    if ctx.used_namespaces.get() {
        decls.splice(0..0, ctx.generate_namespace_type(namespace_ty));
    }

    let attrs = ctx.span_attr(ctx.def_span(def_id)).into_iter().collect();
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Some(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } })
}

/// Translate a logical term to why3.
pub(crate) fn lower_logical_defn<'tcx>(
    ctx: &Why3Generator<'tcx>,
    names: &impl Namer<'tcx>,
    sig: LogicSignature,
    kind: DeclKind,
    body: Term<'tcx>,
    inline: bool,
) -> Vec<Decl> {
    let mut decls = vec![];
    let mut lim_name = None;

    // We don't pull dependencies for FnDef items, because it may be more private than
    // the definition is transparent
    let body = lower_pure_weakdep(ctx, names, &body.spanned());

    if sig.variant.is_none() {
        let mut sig = sig.why_sig.clone();
        sig.contract = Default::default();

        let mut meta_decl = None;
        if inline {
            sig.attrs.push(Attribute::Attr("inline:trivial".into()));
            let kw = match kind {
                DeclKind::Constant => "constant",
                DeclKind::Predicate => "predicate",
                DeclKind::Function => "function",
            };

            meta_decl = Some(Decl::Meta(Meta {
                name: MetaIdent("rewrite_def".into()),
                args: Box::new([MetaArg::Keyword(kw.into()), MetaArg::Name(Name::local(sig.name))]),
            }))
        }

        let decl = match kind {
            DeclKind::Function => Decl::LogicDefn(LogicDefn { sig, body }),
            DeclKind::Predicate => Decl::PredDecl(Predicate { sig, body }),
            DeclKind::Constant => Decl::ConstantDecl(Constant {
                name: sig.name,
                type_: sig.retty.unwrap_or_else(|| ty::bool()),
                body: Some(body),
            }),
        };

        decls.push(decl);
        decls.extend(meta_decl);
    } else {
        let mut decl_sig = sig.why_sig.clone();
        decl_sig.contract = Default::default();

        decls.push(Decl::LogicDecl(LogicDecl { kind: Some(kind), sig: decl_sig }));

        if sig.why_sig.uses_simple_triggers() {
            lim_name = Some(sig.why_sig.name.refresh_with(|s| format!("{s}_lim")));
            limited_function_encode(
                &mut decls,
                &sig.why_sig,
                lim_name.unwrap(),
                body,
                kind,
                inline,
            );
        } else {
            decls.push(Decl::Axiom(definition_axiom(&sig.why_sig, body, "def", inline)));
        }
    }

    if !sig.why_sig.contract.ensures.is_empty() {
        if let Some(lim_name) = lim_name
            && sig.variant.is_some()
        {
            let mut lim_sig = sig.why_sig;
            lim_sig.name = lim_name;
            lim_sig.trigger = Some(Trigger::single(function_call(&lim_sig)));
            lim_sig.attrs = vec![];

            decls.extend(spec_axioms(&lim_sig))
        } else {
            decls.extend(spec_axioms(&sig.why_sig));
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
    inline: bool,
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
    decls.push(Decl::Axiom(definition_axiom(sig, body, "def", inline)));
    decls.push(Decl::Axiom(definition_axiom(sig, lim_call, "def_lim", inline)));
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

fn definition_axiom(sig: &Signature, body: Exp, suffix: &str, rewrite: bool) -> Axiom {
    let call = function_call(sig);
    let trigger = sig.trigger.clone();

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call.clone()), Box::new(body));
    let condition = sig.contract.requires_implies(equation);
    let axiom = Exp::forall_trig(sig.args.clone(), trigger, condition);

    let name = sig.name.refresh_with(|s| format!("{s}_{suffix}"));
    Axiom { name, rewrite, axiom }
}
