use crate::{
    backend::{
        CannotFetchThir, Why3Generator, is_trusted_item, logic::vcgen::wp, signature::sig_to_why3,
        term::lower_pure, ty::translate_ty,
    },
    contracts_items::get_builtin,
    ctx::*,
    naming::ident_of,
    translated_item::FileModule,
    translation::pearlite::Term,
};
use rustc_hir::def_id::DefId;
use why3::{
    Ident,
    declaration::*,
    exp::{BinOp, Exp, ExpMutVisitor, Trigger, super_visit_mut},
};

mod vcgen;

pub(crate) fn translate_logic_or_predicate(
    ctx: &Why3Generator,
    def_id: DefId,
) -> Result<Option<FileModule>, CannotFetchThir> {
    let mut names = Dependencies::new(ctx, def_id);
    let pre_sig = ctx.sig(def_id).clone().normalize(ctx.tcx, ctx.typing_env(def_id));

    if pre_sig.contract.is_empty() {
        return Ok(None);
    }

    // Check that we don't have both `builtins` and a contract at the same time (which are contradictory)
    if get_builtin(ctx.tcx, def_id).is_some() {
        ctx.crash_and_error(
            ctx.def_span(def_id),
            "cannot specify both `creusot::builtins` and a contract on the same definition",
        );
    }

    if !def_id.is_local() || is_trusted_item(ctx.tcx, def_id) || !ctx.has_body(def_id) {
        return Ok(None);
    }

    let mut body_decls = Vec::new();

    let args = pre_sig.inputs.clone();

    let name = names.item(names.self_id, names.self_subst).as_ident();
    let sig = sig_to_why3(ctx, &mut names, name, pre_sig, def_id);
    let (param_decls, args_names): (Vec<_>, Vec<_>) = args
        .into_iter()
        .map(|(nm, span, ty)| {
            let name = ident_of(nm);
            let decl = Decl::LogicDecl(LogicDecl {
                kind: Some(DeclKind::Constant),
                sig: Signature {
                    name: name.clone(),
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
            ItemType::Logic { .. } => LogicDecl { sig, kind: Some(DeclKind::Function) },
            ItemType::Predicate { .. } => {
                sig.retty = None;
                LogicDecl { sig, kind: Some(DeclKind::Predicate) }
            }
            ItemType::Program | ItemType::Closure => LogicDecl { sig, kind: None },
            ItemType::Constant => LogicDecl { sig, kind: Some(DeclKind::Constant) },
            _ => unreachable!(),
        }
    };
    body_decls.push(Decl::LogicDecl(val_decl));

    let postcondition = sig.contract.ensures_conj();

    let term = ctx.ctx.term(def_id)?.unwrap().clone();
    let wp = wp(
        ctx,
        &mut names,
        def_id,
        args_names,
        sig.contract.variant.clone(),
        term,
        "result".into(),
        postcondition.clone(),
    )
    .unwrap_or_else(|e| {
        ctx.fatal_error(e.span(), &format!("translate_logic_or_predicate: {e:?}")).emit()
    });

    let goal = sig.contract.requires_implies(wp);

    body_decls.extend([Decl::Goal(Goal { name: format!("vc_{}", (&*sig.name)).into(), goal })]);

    let mut decls = names.provide_deps(ctx);
    decls.extend(body_decls);

    let attrs = ctx.span_attr(ctx.def_span(def_id)).into_iter().collect();
    let meta = ctx.display_impl_of(def_id);
    let path = ctx.module_path(def_id);
    let name = path.why3_ident();
    Ok(Some(FileModule { path, modl: Module { name, decls: decls.into(), attrs, meta } }))
}

pub(crate) fn lower_logical_defn<'tcx, N: Namer<'tcx>>(
    ctx: &Why3Generator<'tcx>,
    names: &N,
    mut sig: Signature,
    kind: DeclKind,
    body: Term<'tcx>,
) -> Vec<Decl> {
    if let DeclKind::Predicate = kind {
        sig.retty = None;
    }

    let mut decls = vec![];

    let body = lower_pure(ctx, names, &body);

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

        if sig.uses_simple_triggers() {
            limited_function_encode(&mut decls, &sig, body, kind)
        } else {
            decls.push(Decl::Axiom(definition_axiom(&sig, body, "def")));
        }
    }

    if !sig.contract.ensures.is_empty() {
        if sig.uses_simple_triggers() && !sig.contract.variant.is_none() {
            let lim_name = Ident::from_string(format!("{}_lim", &*sig.name));
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
fn limited_function_encode(decls: &mut Vec<Decl>, sig: &Signature, mut body: Exp, kind: DeclKind) {
    let lim_name = Ident::from_string(format!("{}_lim", &*sig.name));
    subst_qname(&mut body, &sig.name, &lim_name);
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

pub(crate) fn spec_axiom(sig: &Signature) -> Axiom {
    let postcondition = sig.contract.ensures_conj();
    let mut condition = sig.contract.requires_implies(postcondition);

    let func_call = function_call(sig);
    let trigger = sig.trigger.clone().into_iter();
    condition.subst(&mut [("result".into(), func_call.clone())].into_iter().collect());
    let args: Box<[(_, _)]> = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .collect();

    let axiom = Exp::forall_trig(args, trigger, condition);

    Axiom { name: format!("{}_spec", &*sig.name).into(), rewrite: false, axiom }
}

pub fn function_call(sig: &Signature) -> Exp {
    let args = sig
        .args
        .iter()
        .cloned()
        .flat_map(|b| b.var_type_pairs())
        .filter(|arg| &*arg.0 != "_")
        .map(|arg| Exp::var(arg.0));

    Exp::var(sig.name.clone()).app(args)
}

fn definition_axiom(sig: &Signature, body: Exp, suffix: &str) -> Axiom {
    let call = function_call(sig);
    let trigger = sig.trigger.clone().into_iter();

    let equation = Exp::BinaryOp(BinOp::Eq, Box::new(call.clone()), Box::new(body));
    let condition = sig.contract.requires_implies(equation);

    let args: Box<[_]> = sig.args.clone().into_iter().flat_map(|b| b.var_type_pairs()).collect();

    let axiom = Exp::forall_trig(args, trigger, condition);

    let name = format!("{}_{suffix}", &*sig.name).into();
    Axiom { name, rewrite: false, axiom }
}
