use crate::{
    backend::{
        TranslationCtx, Why3Generator,
        clone_map::{CloneNames, Dependency, Kind, Namer},
        closures::{closure_hist_inv, closure_post, closure_pre, closure_resolve},
        is_trusted_item,
        logic::{lower_logical_defn, spec_axioms},
        program,
        signature::{lower_logic_sig, lower_program_sig},
        structural_resolve::structural_resolve,
        term::{lower_pure, lower_pure_weakdep},
        ty::{
            eliminator, translate_closure_ty, translate_tuple_ty, translate_ty, translate_tydecl,
        },
        ty_inv::InvariantElaborator,
    },
    contracts_items::{
        get_builtin, get_fn_impl_postcond, get_fn_mut_impl_hist_inv, get_fn_mut_impl_postcond,
        get_fn_once_impl_postcond, get_fn_once_impl_precond, get_resolve_method, is_fn_ghost_ty,
        is_fn_impl_postcond, is_fn_mut_impl_hist_inv, is_fn_mut_impl_postcond,
        is_fn_once_impl_postcond, is_fn_once_impl_precond, is_ghost_deref, is_ghost_deref_mut,
        is_inv_function, is_logic, is_namespace_ty, is_resolve_function, is_size_of_logic,
        is_structural_resolve,
    },
    ctx::{BodyId, ItemType},
    naming::name,
    translation::{
        constant::from_ty_const,
        pearlite::{BinOp, Pattern, QuantKind, SmallRenaming, Term, TermKind, Trigger, normalize},
        specification::Condition,
        traits::TraitResolved,
    },
};
use petgraph::graphmap::DiGraphMap;
use rustc_ast::Mutability;
use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::{
    mir::Promoted,
    ty::{
        self, AliasTyKind, Const, GenericArg, GenericArgsRef, TraitRef, Ty, TyCtxt, TyKind,
        TypeFoldable, TypingEnv, UnevaluatedConst,
    },
};
use rustc_span::{DUMMY_SP, Span};
use rustc_type_ir::{ClosureKind, ConstKind, EarlyBinder};
use std::{
    assert_matches::assert_matches,
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
};
use why3::{
    Ident,
    declaration::{Attribute, Axiom, Decl, DeclKind, LogicDecl, Signature, TyDecl, Use},
};

/// Weak dependencies are allowed to form cycles in the graph, but strong ones cannot,
/// weak dependencies are used to perform an initial stratification of the dependency graph.
#[derive(PartialEq, PartialOrd, Copy, Clone)]
pub enum Strength {
    Weak,
    Strong,
}

/// The `Expander` takes a list of 'root' dependencies (items explicitly requested by user code),
/// and expands this into a complete dependency graph.
pub(super) struct Expander<'a, 'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, Strength>,
    dep_bodies: HashMap<Dependency<'tcx>, Vec<Decl>>,
    namer: &'a mut CloneNames<'tcx>,
    self_key: (DefId, GenericArgsRef<'tcx>),
    typing_env: TypingEnv<'tcx>,
    expansion_queue: VecDeque<(Dependency<'tcx>, Strength, Dependency<'tcx>)>,
    /// Span for the item we are expanding
    root_span: Span,
}

struct ExpansionProxy<'a, 'tcx> {
    namer: &'a mut CloneNames<'tcx>,
    expansion_queue: RefCell<&'a mut VecDeque<(Dependency<'tcx>, Strength, Dependency<'tcx>)>>,
    source: Dependency<'tcx>,
}

impl<'tcx> Namer<'tcx> for ExpansionProxy<'_, 'tcx> {
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, ctx: &TranslationCtx<'tcx>, ty: T) -> T {
        self.namer.normalize(ctx, ty)
    }

    fn raw_dependency(&self, dep: Dependency<'tcx>) -> &Kind {
        self.expansion_queue.borrow_mut().push_back((self.source, Strength::Strong, dep));
        self.namer.raw_dependency(dep)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.namer.tcx()
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        self.namer.typing_env()
    }

    fn span(&self, span: Span) -> Option<Attribute> {
        self.namer.span(span)
    }

    fn bitwise_mode(&self) -> bool {
        self.namer.bitwise_mode()
    }
}

fn expand_program<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Item(def_id, subst);
    let typing_env = elab.typing_env;
    let names = elab.namer(dep);
    let name = names.dependency(dep).ident();

    if ctx.def_kind(def_id) == DefKind::Closure {
        // Inline the body of closures
        let bid = BodyId { def_id: def_id.expect_local(), promoted: None };
        let coma = program::to_why(ctx, &names, name, bid);
        return vec![Decl::Coma(coma)];
    }

    let mut pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx.tcx, typing_env);

    if is_ghost_deref(ctx.tcx, def_id) || is_ghost_deref_mut(ctx.tcx, def_id) {
        // If `Ghost::deref`` or `Ghost::deref_mut` are called direclty, then
        // the validation pass has checked that the call is in the right context.
        // Hence we can remove the precondition `#[requires(false)]` which was protecting
        // against indirect calls (via generics).
        pre_sig.contract.requires.clear();
    }

    if let TraitResolved::UnknownFound = TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst)
                // These conditions are important to make sure the Fn trait familly is implemented
                && ctx.fn_sig(def_id).skip_binder().is_fn_trait_compatible()
                && ctx.codegen_fn_attrs(def_id).target_features.is_empty()
    {
        let fn_name = ctx.item_name(def_id);

        let args =
            Term::tuple(ctx.tcx, pre_sig.inputs.iter().map(|&(nm, _, ty)| Term::var(nm, ty)));
        let fndef_ty = Ty::new_fn_def(ctx.tcx, def_id, subst);

        let pre_post_subst = ctx.mk_args(&[args.ty, fndef_ty].map(GenericArg::from));

        let pre_did = get_fn_once_impl_precond(ctx.tcx);
        let pre = Term::call(ctx.tcx, typing_env, pre_did, pre_post_subst, [
            Term::unit(ctx.tcx).coerce(fndef_ty),
            args.clone(),
        ]);
        let expl_pre = format!("expl:{} requires", fn_name);
        pre_sig.contract.requires = vec![Condition { term: pre, expl: expl_pre }];

        let post_did = get_fn_once_impl_postcond(ctx.tcx);
        let post = Term::call(ctx.tcx, typing_env, post_did, pre_post_subst, [
            Term::unit(ctx.tcx).coerce(fndef_ty),
            args,
            Term::var(name::result(), pre_sig.output),
        ]);
        let expl_post = format!("expl:{} ensures", fn_name);
        pre_sig.contract.ensures = vec![Condition { term: post, expl: expl_post }]
    } else {
        pre_sig.add_type_invariant_spec(ctx, def_id, typing_env)
    }

    let return_ident = Ident::fresh_local("return");
    let (sig, contract, return_ty) =
        lower_program_sig(ctx, &names, name, pre_sig, def_id, return_ident);
    vec![program::val(sig, contract, return_ident, return_ty)]
}

fn expand_promoted<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    def_id: LocalDefId,
    prom: Promoted,
) -> Vec<Decl> {
    let names = elab.namer(Dependency::Promoted(def_id, prom));
    let name = names.dependency(Dependency::Promoted(def_id, prom)).ident();
    // Inline the body of promoteds
    let bid = BodyId { def_id, promoted: Some(prom) };
    let coma = program::to_why(ctx, &names, name, bid);
    vec![Decl::Coma(coma)]
}

/// Expand a logical item
fn expand_logic<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Item(def_id, subst);

    if is_inv_function(ctx.tcx, def_id) {
        elab.expansion_queue.push_back((
            dep,
            Strength::Weak,
            Dependency::TyInvAxiom(subst.type_at(0)),
        ));
    }

    if get_builtin(ctx.tcx, def_id).is_some() {
        match elab.namer.dependency(dep) {
            Kind::Named(_) => return vec![],
            Kind::UsedBuiltin(qname) => {
                if qname.module.is_empty() {
                    return vec![];
                } else {
                    return vec![Decl::UseDecls(Box::new([Use {
                        name: qname.module.clone(),
                        export: false,
                    }]))];
                }
            }
            Kind::Unnamed => unreachable!(),
        }
    }

    let typing_env = elab.typing_env;
    let pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx.tcx, typing_env);

    let bound: Box<[Ident]> = pre_sig.inputs.iter().map(|(ident, _, _)| ident.0).collect();
    let trait_resol = TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst);
    assert_matches!(
        trait_resol,
        TraitResolved::NotATraitItem
            | TraitResolved::Instance { .. } // The default impl is known to be the final instance
            | TraitResolved::UnknownFound // Unresolved trait method
    );
    // The other case are impossible, because that would mean we are not guaranteed to have an instance

    let opaque = matches!(trait_resol, TraitResolved::UnknownFound)
        || !ctx.is_transparent_from(def_id, elab.self_key.0);

    let names = elab.namer(dep);
    let name = names.dependency(dep).ident();
    let sig = lower_logic_sig(ctx, &names, name, pre_sig, def_id);
    let kind = match ctx.item_type(def_id) {
        ItemType::Logic { .. } if sig.args.is_empty() && sig.retty != None => DeclKind::Constant,
        ItemType::Logic { .. } if sig.retty == None => DeclKind::Predicate,
        ItemType::Logic { .. } => DeclKind::Function,
        ItemType::Constant => DeclKind::Constant,
        _ => unreachable!(),
    };
    if !opaque && let Some(term) = term(ctx, typing_env, &bound, def_id, subst) {
        lower_logical_defn(ctx, &names, sig, kind, term)
    } else {
        let mut decls = val(sig, kind);

        if is_fn_once_impl_precond(ctx.tcx, def_id) {
            if let &TyKind::FnDef(did_f, subst_f) = subst.type_at(1).kind() {
                let args_id = Ident::fresh_local("args").into();
                let args = Term::var(args_id, subst.type_at(0));
                if let Some(pre) = pre_fndef(ctx, typing_env, did_f, subst_f, args.clone()) {
                    let call = Term::call(ctx.tcx, typing_env, def_id, subst, [
                        Term::unit(ctx.tcx).coerce(subst.type_at(1)),
                        args,
                    ]);
                    let trig = Box::new([Trigger(Box::new([call.clone()]))]);
                    let axiom = pre.implies(call).forall_trig((args_id, subst.type_at(0)), trig);
                    decls.push(Decl::Axiom(Axiom {
                        name: Ident::fresh(ctx.crate_name(), "precondition_fndef"),
                        rewrite: false,
                        axiom: lower_pure(ctx, &names, &axiom),
                    }))
                }
            }
        } else if is_fn_impl_postcond(ctx.tcx, def_id)
            || is_fn_mut_impl_postcond(ctx.tcx, def_id)
            || is_fn_once_impl_postcond(ctx.tcx, def_id)
        {
            if let &TyKind::FnDef(did_f, subst_f) = subst.type_at(1).kind() {
                let args_id = Ident::fresh_local("args").into();
                let args = Term::var(args_id, subst.type_at(0));

                let res_id = Ident::fresh_local("res").into();
                let res_ty = ctx.instantiate_bound_regions_with_erased(
                    ctx.fn_sig(did_f).instantiate(ctx.tcx, subst_f).output(),
                );
                let res = Term::var(res_id, res_ty);
                if let Some(post) =
                    post_fndef(ctx, typing_env, did_f, subst_f, args.clone(), res.clone())
                {
                    let mut v = vec![Term::unit(ctx.tcx).coerce(subst.type_at(1)), args, res];
                    if is_fn_mut_impl_postcond(ctx.tcx, def_id) {
                        v.insert(2, v[0].clone());
                    }
                    let call = Term::call(ctx.tcx, typing_env, def_id, subst, v);
                    let trig = Box::new([Trigger(Box::new([call.clone()]))]);
                    let axiom = call.implies(post).quant(
                        QuantKind::Forall,
                        Box::new([(args_id, subst.type_at(0)), (res_id, res_ty)]),
                        trig,
                    );
                    decls.push(Decl::Axiom(Axiom {
                        name: Ident::fresh(ctx.crate_name(), "postcondition_fndef"),
                        rewrite: false,
                        axiom: lower_pure(ctx, &names, &axiom),
                    }))
                }
            }
        }

        decls
    }
}

// TODO Deprecate and fold into LogicElab
fn expand_ty_inv_axiom<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let param_env = elab.typing_env;
    let span = elab.root_span;
    let names = elab.namer(Dependency::TyInvAxiom(ty));
    let mut elab = InvariantElaborator::new(param_env, ctx);
    let Some(term) = elab.elaborate_inv(ty, span) else { return vec![] };
    let rewrite = elab.rewrite;
    let axiom = lower_pure_weakdep(ctx, &names, &term);
    let axiom =
        Axiom { name: names.dependency(Dependency::TyInvAxiom(ty)).ident(), rewrite, axiom };
    vec![Decl::Axiom(axiom)]
}

fn expand_type<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let dep = Dependency::Type(ty);
    let typing_env = elab.typing_env;
    let names = elab.namer(dep);
    match ty.kind() {
        TyKind::Param(_) => vec![Decl::TyDecl(TyDecl::Opaque {
            ty_name: names.ty(ty).to_ident(),
            ty_params: Box::new([]),
        })],
        TyKind::Alias(AliasTyKind::Opaque | AliasTyKind::Projection, _) => {
            let (def_id, subst) = dep.did().unwrap();
            vec![Decl::TyDecl(TyDecl::Opaque {
                ty_name: names.def_ty(def_id, subst).to_ident(),
                ty_params: Box::new([]),
            })]
        }
        TyKind::Closure(did, subst) => translate_closure_ty(ctx, &names, *did, subst),
        TyKind::Adt(adt_def, subst) if get_builtin(ctx.tcx, adt_def.did()).is_some() => {
            for ty in subst.types() {
                translate_ty(ctx, &names, DUMMY_SP, ty);
            }
            if let Kind::UsedBuiltin(qname) = names.dependency(dep)
                && !qname.module.is_empty()
            {
                vec![Decl::UseDecls(Box::new([Use { name: qname.module.clone(), export: false }]))]
            } else {
                vec![]
            }
        } // Special treatment for the `Namespace` type: we must generate it after collecting all the possible variants.
        TyKind::Adt(adt_def, _) if is_namespace_ty(ctx.tcx, adt_def.did()) => {
            ctx.used_namespaces.set(true);
            Vec::new()
        }
        TyKind::Adt(_, _) => {
            let (def_id, subst) = dep.did().unwrap();
            translate_tydecl(ctx, &names, (def_id, subst), typing_env)
        }
        TyKind::Tuple(_) => translate_tuple_ty(ctx, &names, ty),
        _ => unreachable!("unsupported type: {ty}"),
    }
}

impl<'a, 'tcx> Expander<'a, 'tcx> {
    /// # Parameters
    ///
    /// `span`: span of the item being expanded
    pub(crate) fn new(
        namer: &'a mut CloneNames<'tcx>,
        self_key: (DefId, GenericArgsRef<'tcx>),
        typing_env: TypingEnv<'tcx>,
        initial: impl Iterator<Item = Dependency<'tcx>>,
        span: Span,
    ) -> Self {
        Self {
            graph: Default::default(),
            namer,
            self_key,
            typing_env,
            expansion_queue: initial
                .map(|b| (Dependency::Item(self_key.0, self_key.1), Strength::Strong, b))
                .collect(),
            dep_bodies: Default::default(),
            root_span: span,
        }
    }

    fn namer(&mut self, source: Dependency<'tcx>) -> ExpansionProxy<'_, 'tcx> {
        ExpansionProxy {
            namer: self.namer,
            expansion_queue: RefCell::new(&mut self.expansion_queue),
            source,
        }
    }

    /// Expand the graph with new entries
    pub fn update_graph(
        mut self,
        ctx: &Why3Generator<'tcx>,
    ) -> (DiGraphMap<Dependency<'tcx>, Strength>, HashMap<Dependency<'tcx>, Vec<Decl>>) {
        let mut visited = HashSet::new();
        while let Some((s, strength, t)) = self.expansion_queue.pop_front() {
            if let Some(old) = self.graph.add_edge(s, t, strength)
                && old > strength
            {
                self.graph.add_edge(s, t, old);
            }

            if !visited.insert(t) {
                continue;
            }
            self.expand(ctx, t);
        }

        (self.graph, self.dep_bodies)
    }

    fn expand(&mut self, ctx: &Why3Generator<'tcx>, dep: Dependency<'tcx>) {
        expand_laws(self, ctx, dep);

        let decls = match dep {
            Dependency::Type(ty) => expand_type(self, ctx, ty),
            Dependency::Item(def_id, subst) => {
                if matches!(ctx.item_type(def_id), ItemType::Constant | ItemType::Logic { .. }) {
                    expand_logic(self, ctx, def_id, subst)
                } else if matches!(ctx.def_kind(def_id), DefKind::Field | DefKind::Variant) {
                    self.namer(dep).def_ty(ctx.parent(def_id), subst);
                    vec![]
                } else {
                    expand_program(self, ctx, def_id, subst)
                }
            }
            Dependency::TyInvAxiom(ty) => expand_ty_inv_axiom(self, ctx, ty),
            Dependency::ClosureAccessor(_, _, _) | Dependency::TupleField(_, _) => vec![],
            Dependency::PreMod(b) => {
                vec![Decl::UseDecls(Box::new([Use {
                    name: self.namer.prelude_module_name(b),
                    export: false,
                }]))]
            }
            Dependency::Eliminator(def_id, subst) => {
                vec![eliminator(ctx, &self.namer(dep), def_id, subst)]
            }
            Dependency::Promoted(def_id, prom) => expand_promoted(self, ctx, def_id, prom),
        };

        self.dep_bodies.insert(dep, decls);
    }
}

fn traitref_of_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<TraitRef<'tcx>> {
    let ai = tcx.opt_associated_item(did)?;
    let cont = ai.container_id(tcx);
    let subst = tcx.mk_args_from_iter(subst.iter().take(tcx.generics_of(cont).count()));

    if tcx.def_kind(cont) == DefKind::Trait {
        return Some(TraitRef::new(tcx, cont, subst));
    }

    let trait_ref = tcx.impl_trait_ref(cont)?.instantiate(tcx, subst);
    Some(tcx.normalize_erasing_regions(typing_env, trait_ref))
}

fn expand_laws<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    dep: Dependency<'tcx>,
) {
    let (self_did, self_subst) = elab.self_key;
    let Some((item_did, item_subst)) = dep.did() else {
        return;
    };

    let Some(item_ai) = ctx.opt_associated_item(item_did) else { return };
    let item_container = item_ai.container_id(ctx.tcx);

    // Dont clone laws into the trait / impl which defines them.
    if let Some(tr_item) = traitref_of_item(ctx.tcx, elab.typing_env, item_did, item_subst)
        && let Some(tr_self) = traitref_of_item(ctx.tcx, elab.typing_env, self_did, self_subst)
        && tr_item == tr_self
    {
        return;
    }

    // TODO: Push out of graph expansion
    // If the function we are cloning into is `#[trusted]` there is no need for laws.
    // Similarily, if it has no body, there will be no proofs.
    if is_trusted_item(ctx.tcx, self_did) || !ctx.has_body(self_did) {
        return;
    }

    for law in ctx.laws(item_container) {
        let law_dep = elab.namer(dep).resolve_dependency(Dependency::Item(*law, item_subst));
        // We add a weak dep from `dep` to make sure it appears close to the triggering item
        elab.expansion_queue.push_back((dep, Strength::Weak, law_dep));
    }
}

fn val(mut sig: Signature, kind: DeclKind) -> Vec<Decl> {
    if let DeclKind::Predicate = kind {
        sig.retty = None;
    }
    let mut d = spec_axioms(&sig).collect::<Vec<_>>();
    sig.contract = Default::default();
    d.insert(0, Decl::LogicDecl(LogicDecl { kind: Some(kind), sig }));
    d
}

/// Generate body of `resolve` for `FnMut` closures.
fn resolve_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let trait_meth_id = get_resolve_method(ctx.tcx);
    let sig = ctx.sig(def_id).clone();
    let mut pre_sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
    pre_sig = pre_sig.normalize(ctx.tcx, typing_env);

    let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);

    if let &TyKind::Closure(def_id, subst) = subst[0].as_type().unwrap().kind() {
        Some(closure_resolve(ctx, def_id, subst, bound))
    } else {
        match TraitResolved::resolve_item(ctx.tcx, typing_env, trait_meth_id, subst) {
            TraitResolved::NotATraitItem => unreachable!(),
            TraitResolved::Instance { def: (meth_did, meth_substs), .. } => {
                // We know the instance => body points to it
                Some(Term::call(ctx.tcx, typing_env, meth_did, meth_substs, [arg]))
            }
            TraitResolved::UnknownFound | TraitResolved::UnknownNotFound => {
                // We don't know the instance => body is opaque
                None
            }
            TraitResolved::NoInstance => {
                // We know there is no instance => body is true
                Some(Term::true_(ctx.tcx))
            }
        }
    }
}

/// Generate body of `postcondition_once` for `FnMut` closures.
fn fn_once_postcond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let tcx = ctx.tcx;
    let &[self_, args, result] = bound else {
        panic!("postcondition_once must have 3 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(get_fn_once_impl_postcond(tcx)).inputs[2].2),
    );
    let res = Term::var(result, ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => {
            let mut post =
                closure_post(ctx, ClosureKind::FnOnce, did.expect_local(), self_, args, None);
            post.subst(&SmallRenaming([(name::result(), result)]));
            Some(post)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if is_fn_ghost_ty(tcx, def.did()) => {
            let mut subst_postcond = subst.to_vec();
            let closure_ty = def.all_fields().next().unwrap().ty(tcx, subst_inner);
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, [
                Term {
                    ty: closure_ty,
                    span: self_.span,
                    kind: TermKind::Projection { lhs: Box::new(self_), idx: 0usize.into() },
                },
                args,
                res,
            ]))
        }
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(
                ctx.tcx,
                typing_env,
                get_fn_mut_impl_postcond(ctx.tcx),
                subst_postcond,
                [self_.clone().cur(), args, self_.fin(), res],
            ))
        }
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(ctx.tcx, typing_env, get_fn_impl_postcond(ctx.tcx), subst_postcond, [
                self_.coerce(*cl),
                args,
                res,
            ]))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = bsubst[0];
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(
                ctx.tcx,
                typing_env,
                get_fn_once_impl_postcond(ctx.tcx),
                subst_postcond,
                [self_.coerce(bsubst.type_at(0)), args, res],
            ))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            post_fndef(ctx, typing_env, did, subst, args, res)
        }
        _ => None,
    }
}

/// Generate body of `postcondition_mut` for `FnMut` closures.
fn fn_mut_postcond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let &[self_, args, result_state, result] = bound else {
        panic!("postcondition_mut must have 4 arguments. This should not happen. Found: {bound:?}")
    };
    let tcx = ctx.tcx;
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));
    let result_state = Term::var(result_state, ty_self);
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(get_fn_mut_impl_postcond(tcx)).inputs[3].2),
    );
    let res = Term::var(result, ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => {
            let mut post = closure_post(
                ctx,
                ClosureKind::FnMut,
                did.expect_local(),
                self_,
                args,
                Some(result_state),
            );
            post.subst(&SmallRenaming([(name::result(), result)]));
            Some(post)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if is_fn_ghost_ty(tcx, def.did()) => {
            let mut subst_postcond = subst.to_vec();
            let closure_ty = def.all_fields().next().unwrap().ty(tcx, subst_inner);
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(
                Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, [
                    Term {
                        ty: closure_ty,
                        kind: TermKind::Projection {
                            lhs: Box::new(self_.clone()),
                            idx: 0usize.into(),
                        },
                        span: self_.span,
                    },
                    args,
                    res,
                ])
                .conj(self_.eq(ctx.tcx, result_state)),
            )
        }
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(
                Term::call(tcx, typing_env, get_fn_mut_impl_postcond(tcx), subst_postcond, [
                    self_.clone().cur(),
                    args,
                    result_state.clone().cur(),
                    res,
                ])
                .conj(self_.fin().eq(ctx.tcx, result_state.fin())),
            )
        }
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(
                Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, [
                    self_.clone().coerce(*cl),
                    args,
                    res,
                ])
                .conj(self_.eq(ctx.tcx, result_state)),
            )
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = bsubst[0];
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(tcx, typing_env, get_fn_mut_impl_postcond(tcx), subst_postcond, [
                self_.coerce(bsubst.type_at(0)),
                args,
                result_state.coerce(bsubst.type_at(0)),
                res,
            ]))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            post_fndef(ctx, typing_env, did, subst, args, res)
        }
        _ => None,
    }
}

/// Generate body of `postcondition` for `Fn` closures.
fn fn_postcond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let tcx = ctx.tcx;
    let &[self_, args, result] = bound else {
        panic!("postcondition must have 3 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(get_fn_impl_postcond(tcx)).inputs[2].2),
    );
    let res = Term::var(result, ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => {
            let mut post =
                closure_post(ctx, ClosureKind::Fn, did.expect_local(), self_, args, None);
            post.subst(&SmallRenaming([(name::result(), result)]));
            Some(post)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if is_fn_ghost_ty(tcx, def.did()) => {
            let closure_ty = def.all_fields().next().unwrap().ty(tcx, subst_inner);
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, [
                Term {
                    ty: closure_ty,
                    kind: TermKind::Projection { lhs: Box::new(self_.clone()), idx: 0usize.into() },
                    span: self_.span,
                },
                args,
                res,
            ]))
        }
        &TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(cl);
            let subst_postcond = tcx.mk_args(&subst_postcond);
            Some(Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, [
                self_.clone().coerce(cl),
                args,
                res,
            ]))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = bsubst[0];
            let subst_postcond = tcx.mk_args(&subst_postcond);
            Some(Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, [
                self_.coerce(bsubst.type_at(0)),
                args,
                res,
            ]))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            post_fndef(ctx, typing_env, did, subst, args, res)
        }
        _ => None,
    }
}

fn post_fndef<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Term<'tcx>,
    res: Term<'tcx>,
) -> Option<Term<'tcx>> {
    if is_logic(ctx.tcx, did) {
        return None;
    }

    let mut sig = EarlyBinder::bind(ctx.sig(did).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx.tcx, typing_env);
    sig.add_type_invariant_spec(ctx, did, typing_env);
    let mut post = sig.contract.ensures_conj(ctx.tcx);
    post.subst(&HashMap::from([(name::result(), res.kind)]));
    let pattern = Pattern::tuple(
        sig.inputs.iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
        args.ty,
    );
    Some(Term::let_(pattern, args, post).span(ctx.def_span(did)))
}

/// Generate body of `precondition_once` for `FnOnce` closures.
fn fn_once_precond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let tcx = ctx.tcx;
    let &[self_, args] = bound else {
        panic!("precondition_once must have 2 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);
    let self_ = Term::var(self_, ty_self);
    let args = Term::var(args, subst.type_at(0));

    match ty_self.kind() {
        TyKind::Closure(did, _) => Some(closure_pre(ctx, did.expect_local(), self_, args)),
        &TyKind::Ref(_, cl, m) => {
            let mut subst_pre = subst.to_vec();
            subst_pre[1] = GenericArg::from(cl);
            let subst_pre = ctx.mk_args(&subst_pre);
            let self_ = if m == Mutability::Mut { self_.clone().cur() } else { self_.coerce(cl) };
            Some(Term::call(ctx.tcx, typing_env, get_fn_once_impl_precond(ctx.tcx), subst_pre, [
                self_, args,
            ]))
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let mut subst_pre = subst.to_vec();
            subst_pre[1] = bsubst[0];
            let subst_pre = ctx.mk_args(&subst_pre);
            Some(Term::call(ctx.tcx, typing_env, get_fn_once_impl_precond(ctx.tcx), subst_pre, [
                self_.coerce(bsubst.type_at(0)),
                args,
            ]))
        }
        &TyKind::FnDef(mut did, mut subst) => {
            match TraitResolved::resolve_item(ctx.tcx, typing_env, did, subst) {
                TraitResolved::NotATraitItem => (),
                TraitResolved::Instance { def, .. } => (did, subst) = def,
                TraitResolved::UnknownFound => return None,
                TraitResolved::UnknownNotFound | TraitResolved::NoInstance => unreachable!(),
            }
            pre_fndef(ctx, typing_env, did, subst, args)
        }
        // Handle `FnGhostWrapper`
        TyKind::Adt(def, subst_inner) if is_fn_ghost_ty(tcx, def.did()) => {
            let mut subst_postcond = subst.to_vec();
            let closure_ty = def.all_fields().next().unwrap().ty(tcx, subst_inner);
            subst_postcond[1] = GenericArg::from(closure_ty);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            Some(Term::call(ctx.tcx, typing_env, get_fn_once_impl_precond(tcx), subst_postcond, [
                Term {
                    ty: closure_ty,
                    kind: TermKind::Projection { lhs: Box::new(self_.clone()), idx: 0usize.into() },
                    span: self_.span,
                },
                args,
            ]))
        }
        _ => None,
    }
}

fn pre_fndef<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    did: DefId,
    subst: GenericArgsRef<'tcx>,
    args: Term<'tcx>,
) -> Option<Term<'tcx>> {
    if is_logic(ctx.tcx, did) {
        // This is especially important for Snapshot::deref, which should keep have a false
        // precondition if called in a program via a generic.
        return None;
    }
    let mut sig = EarlyBinder::bind(ctx.sig(did).clone())
        .instantiate(ctx.tcx, subst)
        .normalize(ctx.tcx, typing_env);
    sig.add_type_invariant_spec(ctx, did, typing_env);
    let pre = sig.contract.requires_conj(ctx.tcx);
    let pattern = Pattern::tuple(
        sig.inputs.iter().map(|&(nm, span, ty)| Pattern::binder_sp(nm, span, ty)),
        args.ty,
    );
    Some(Term::let_(pattern, args, pre).span(ctx.def_span(did)))
}

fn fn_mut_hist_inv_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
    bound: &[Ident],
) -> Option<Term<'tcx>> {
    let &[self_, future] = bound else {
        panic!("hist_inv must have 2 arguments. This should not happen. Found: {bound:?}")
    };
    let ty_self = subst.type_at(1);

    match ty_self.kind() {
        TyKind::Closure(did, _) => Some(closure_hist_inv(
            ctx,
            did.expect_local(),
            Term::var(self_, ty_self),
            Term::var(future, ty_self),
        )),
        TyKind::Ref(_, _, Mutability::Not) => {
            Some(Term::var(self_, ty_self).eq(ctx.tcx, Term::var(future, ty_self)))
        }
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let hist_inv = get_fn_mut_impl_hist_inv(ctx.tcx);
            let mut subst_hist_inv = subst.to_vec();
            subst_hist_inv[1] = GenericArg::from(*cl);
            let subst_hist_inv = ctx.mk_args(&subst_hist_inv);
            Some(
                Term::call(ctx.tcx, typing_env, hist_inv, subst_hist_inv, [
                    Term::var(self_, ty_self).cur(),
                    Term::var(future, ty_self).cur(),
                ])
                .conj(
                    Term::var(self_, ty_self).fin().eq(ctx.tcx, Term::var(future, ty_self).fin()),
                ),
            )
        }
        TyKind::Adt(def, bsubst) if def.is_box() => {
            let hist_inv = get_fn_mut_impl_hist_inv(ctx.tcx);
            let mut subst_hist_inv = subst.to_vec();
            subst_hist_inv[1] = bsubst[0];
            let subst_hist_inv = ctx.mk_args(&subst_hist_inv);
            Some(Term::call(ctx.tcx, typing_env, hist_inv, subst_hist_inv, [
                Term::var(self_, ty_self).coerce(bsubst.type_at(0)),
                Term::var(future, ty_self).coerce(bsubst.type_at(0)),
            ]))
        }
        TyKind::FnDef(_, _) => Some(Term::true_(ctx.tcx)),
        _ => None,
    }
}

/// Special definition for `::creusot_contracts::std::mem::size_of_logic`.
///
/// The specification of sizes is documented at [`size_of`].
/// Note: at this point we are guaranteed to have a `Sized` type.
///
/// [`size_of`]: https://doc.rust-lang.org/std/mem/fn.size_of.html
fn size_of_logic_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    use rustc_type_ir::TyKind::*;
    let int_ty = ctx.sig(def_id).output;
    let arg = subst.type_at(0);
    if let Ok(layout) = ctx.tcx.layout_of(ty::PseudoCanonicalInput { typing_env, value: arg }) {
        // Rustc has computed a concrete size for this type. Just use it.
        // This handles at least primitive types, references, pointers, and ZSTs.
        return Some(Term::int(int_ty, layout.size.bytes() as i128));
    }
    match arg.kind() {
        Array(t, n) => size_of_array(ctx, typing_env, def_id, *t, n, int_ty),
        _ => None, // TODO: Adts that are repr(C)
    }
}

fn size_of_array<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    ty: Ty<'tcx>,
    n: &Const<'tcx>,
    int_ty: Ty<'tcx>,
) -> Option<Term<'tcx>> {
    let n = match n.kind() {
        ConstKind::Value(_, ty::ValTree::Leaf(scalar)) => scalar.to_target_usize(ctx.tcx) as i128,
        // TODO: ConstKind::Param
        _ => return None,
    };
    let subst = ctx.mk_args(&[ty.into()]);
    let item_size = Term::call(ctx.tcx, typing_env, def_id, subst, []);
    Some(item_size.bin_op(int_ty, BinOp::Mul, Term::int(int_ty, n)))
}

/// Returns a resolved and normalized term for a dependency.
///
/// Currently, it does not handle invariant axioms but otherwise returns all logical terms.
fn term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    bound: &[Ident],
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    if is_trusted_item(ctx.tcx, def_id) {
        if is_resolve_function(ctx.tcx, def_id) {
            resolve_term(ctx, typing_env, def_id, subst, bound)
        } else if is_structural_resolve(ctx.tcx, def_id) {
            let subj = ctx.sig(def_id).inputs[0].0.0;
            structural_resolve(ctx, typing_env, subj, subst.type_at(0))
        } else if is_fn_once_impl_postcond(ctx.tcx, def_id) {
            fn_once_postcond_term(ctx, typing_env, subst, bound)
        } else if is_fn_mut_impl_postcond(ctx.tcx, def_id) {
            fn_mut_postcond_term(ctx, typing_env, subst, bound)
        } else if is_fn_impl_postcond(ctx.tcx, def_id) {
            fn_postcond_term(ctx, typing_env, subst, bound)
        } else if is_fn_once_impl_precond(ctx.tcx, def_id) {
            fn_once_precond_term(ctx, typing_env, subst, bound)
        } else if is_fn_mut_impl_hist_inv(ctx.tcx, def_id) {
            fn_mut_hist_inv_term(ctx, typing_env, subst, bound)
        } else if is_size_of_logic(ctx.tcx, def_id) {
            size_of_logic_term(ctx, typing_env, def_id, subst)
        } else {
            None
        }
    } else if matches!(ctx.item_type(def_id), ItemType::Constant) {
        let ct = UnevaluatedConst::new(def_id, subst);
        let constant = Const::new(ctx.tcx, ConstKind::Unevaluated(ct));
        let ty = ctx.type_of(def_id).instantiate(ctx.tcx, subst);
        let ty = ctx.tcx.normalize_erasing_regions(typing_env, ty);
        let span = ctx.def_span(def_id);
        let res = from_ty_const(&ctx.ctx, constant, ty, typing_env, span);
        Some(res)
    } else {
        let term = ctx.term(def_id).unwrap().rename(bound);
        let term =
            normalize(ctx.tcx, typing_env, EarlyBinder::bind(term).instantiate(ctx.tcx, subst));
        Some(term)
    }
}
