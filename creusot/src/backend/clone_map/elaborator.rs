use std::{
    cell::RefCell,
    collections::{HashMap, HashSet, VecDeque},
};

use crate::{
    backend::{
        Namer, TranslationCtx, Why3Generator,
        clone_map::{CloneNames, Dependency, Kind},
        is_trusted_function,
        logic::{lower_logical_defn, spec_axiom},
        program,
        signature::sig_to_why3,
        structural_resolve::structural_resolve,
        term::lower_pure,
        ty::{eliminator, translate_closure_ty, translate_ty, translate_tydecl},
        ty_inv::InvariantElaborator,
    },
    constant::from_ty_const,
    contracts_items::{
        get_builtin, get_fn_impl_postcond, get_fn_mut_impl_postcond, get_fn_once_impl_postcond,
        get_resolve_method, is_fn_impl_postcond, is_fn_mut_impl_postcond, is_fn_mut_impl_unnest,
        is_fn_once_impl_postcond, is_fn_once_impl_precond, is_inv_function, is_resolve_function,
        is_structural_resolve,
    },
    ctx::{BodyId, ItemType},
    function::closure_resolve,
    pearlite::{Term, normalize},
    traits::{self, TraitResolved},
};
use petgraph::graphmap::DiGraphMap;
use rustc_ast::Mutability;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{
    Const, GenericArg, GenericArgsRef, TraitRef, Ty, TyCtxt, TyKind, TypeFoldable, TypingEnv,
    UnevaluatedConst,
};
use rustc_span::{DUMMY_SP, Span, Symbol};
use rustc_type_ir::{ConstKind, EarlyBinder};
use why3::declaration::{Attribute, Axiom, Decl, DeclKind, LogicDecl, Signature, TyDecl, Use};

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
    self_key: Dependency<'tcx>,
    typing_env: TypingEnv<'tcx>,
    expansion_queue: VecDeque<(Dependency<'tcx>, Strength, Dependency<'tcx>)>,
}

struct ExpansionProxy<'a, 'tcx> {
    namer: &'a mut CloneNames<'tcx>,
    expansion_queue: RefCell<&'a mut VecDeque<(Dependency<'tcx>, Strength, Dependency<'tcx>)>>,
    source: Dependency<'tcx>,
}

impl<'a, 'tcx> Namer<'tcx> for ExpansionProxy<'a, 'tcx> {
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>>>(&self, ctx: &TranslationCtx<'tcx>, ty: T) -> T {
        self.namer.normalize(ctx, ty)
    }

    fn dependency(&self, dep: Dependency<'tcx>) -> &Kind {
        let dep = dep.erase_regions(self.tcx());
        self.expansion_queue.borrow_mut().push_back((self.source, Strength::Strong, dep));
        self.namer.dependency(dep)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.namer.tcx()
    }

    fn span(&self, span: Span) -> Option<Attribute> {
        self.namer.span(span)
    }

    fn bitwise_mode(&self) -> bool {
        self.namer.bitwise_mode()
    }
}

trait DepElab {
    // type Sig;
    // type Contract;
    // type Body;

    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<Decl>;
}

struct ProgElab;

impl DepElab for ProgElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<Decl> {
        let typing_env = elab.typing_env;
        let mut names = elab.namer(dep);
        let name = names.dependency(dep).ident();

        if let Dependency::Item(def_id, subst) = dep
            && ctx.def_kind(def_id) != DefKind::Closure
        {
            let pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
                .instantiate(ctx.tcx, subst)
                .normalize(ctx.tcx, typing_env);
            let sig = sig_to_why3(ctx, &mut names, name, pre_sig, def_id);
            return vec![program::val(ctx, sig)];
        }

        // Inline the body of closures and promoted
        let bid = match dep {
            Dependency::Item(def_id, _) => BodyId { def_id: def_id.expect_local(), promoted: None },
            Dependency::Promoted(def_id, prom) => BodyId { def_id, promoted: Some(prom) },
            _ => unreachable!(),
        };

        let coma = program::to_why(ctx, &mut names, name, bid);
        vec![Decl::Coma(coma)]
    }
}

struct LogicElab;

impl DepElab for LogicElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<Decl> {
        assert!(matches!(dep, Dependency::Item(_, _)));

        let (def_id, subst) = dep.did().unwrap();

        if is_inv_function(ctx.tcx, def_id) {
            elab.expansion_queue.push_back((
                dep,
                Strength::Weak,
                Dependency::TyInvAxiom(subst.type_at(0)),
            ));
        }

        let kind = match ctx.item_type(def_id) {
            ItemType::Logic { .. } => DeclKind::Function,
            ItemType::Predicate { .. } => DeclKind::Predicate,
            ItemType::Constant => DeclKind::Constant,
            _ => unreachable!(),
        };

        if get_builtin(ctx.tcx, def_id).is_some() {
            match elab.namer.dependency(dep) {
                Kind::Named(_) => return vec![],
                Kind::UsedBuiltin(qname) => {
                    return vec![Decl::UseDecls(Box::new([Use {
                        name: qname.module.clone(),
                        as_: None,
                        export: false,
                    }]))];
                }
                Kind::Unnamed => unreachable!(),
            }
        }

        let typing_env = elab.typing_env;
        let pre_sig = EarlyBinder::bind(ctx.sig(def_id).clone())
            .instantiate(ctx.tcx, subst)
            .normalize(ctx.tcx, typing_env);

        let trait_resol = ctx
            .tcx
            .trait_of_item(def_id)
            .map(|_| traits::TraitResolved::resolve_item(ctx.tcx, typing_env, def_id, subst));

        let is_opaque = matches!(
            trait_resol,
            Some(traits::TraitResolved::UnknownFound | traits::TraitResolved::UnknownNotFound)
        ) || !ctx.is_transparent_from(def_id, elab.self_key.did().unwrap().0)
            || is_trusted_function(ctx.tcx, def_id);

        let mut names = elab.namer(dep);
        let name = names.dependency(dep).ident();
        let sig = sig_to_why3(ctx, &mut names, name, pre_sig, def_id);
        if !is_opaque && let Some(term) = term(ctx, typing_env, dep) {
            lower_logical_defn(ctx, &mut names, sig, kind, term)
        } else {
            val(sig, kind)
        }
    }
}

// TODO Deprecate and fold into LogicElab
fn expand_ty_inv_axiom<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let param_env = elab.typing_env;
    let mut names = elab.namer(Dependency::TyInvAxiom(ty));

    let mut elab = InvariantElaborator::new(param_env, ctx);
    let Some(term) = elab.elaborate_inv(ty, false) else { return vec![] };
    let rewrite = elab.rewrite;
    let exp = lower_pure(ctx, &mut names, &term);
    let axiom =
        Axiom { name: names.dependency(Dependency::TyInvAxiom(ty)).ident(), rewrite, axiom: exp };
    vec![Decl::Axiom(axiom)]
}

struct TyElab;

use rustc_middle::ty::AliasTyKind;

impl DepElab for TyElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<Decl> {
        let Dependency::Type(ty) = dep else { unreachable!() };
        let param_env = elab.typing_env;
        let mut names = elab.namer(dep);
        match ty.kind() {
            TyKind::Param(_) => vec![Decl::TyDecl(TyDecl::Opaque {
                ty_name: names.ty_param(ty).as_ident(),
                ty_params: Box::new([]),
            })],
            TyKind::Alias(AliasTyKind::Opaque | AliasTyKind::Projection, _) => {
                let (def_id, subst) = dep.did().unwrap();
                vec![Decl::TyDecl(TyDecl::Opaque {
                    ty_name: names.ty(def_id, subst).as_ident(),
                    ty_params: Box::new([]),
                })]
            }
            TyKind::Closure(did, subst) => translate_closure_ty(ctx, &mut names, *did, subst)
                .map_or(vec![], |d| vec![Decl::TyDecl(d)]),
            TyKind::Adt(adt_def, subst) if get_builtin(ctx.tcx, adt_def.did()).is_some() => {
                for ty in subst.types() {
                    translate_ty(ctx, &mut names, DUMMY_SP, ty);
                }
                if let Kind::UsedBuiltin(qname) = names.dependency(dep) {
                    vec![Decl::UseDecls(Box::new([Use {
                        as_: None,
                        name: qname.module.clone(),
                        export: false,
                    }]))]
                } else {
                    vec![]
                }
            }
            TyKind::Adt(_, _) => {
                let (def_id, subst) = dep.did().unwrap();
                translate_tydecl(ctx, &mut names, (def_id, subst), param_env)
            }
            _ => unreachable!(),
        }
    }
}

impl<'a, 'tcx> Expander<'a, 'tcx> {
    pub fn new(
        namer: &'a mut CloneNames<'tcx>,
        self_key: Dependency<'tcx>,
        typing_env: TypingEnv<'tcx>,
        initial: impl Iterator<Item = Dependency<'tcx>>,
    ) -> Self {
        Self {
            graph: Default::default(),
            namer,
            self_key,
            typing_env,
            expansion_queue: initial.map(|b| (self_key, Strength::Strong, b)).collect(),
            dep_bodies: Default::default(),
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
        while let Some((s, strength, mut t)) = self.expansion_queue.pop_front() {
            if let Dependency::Item(item, substs) = t
                && ctx.trait_of_item(item).is_some()
                && let TraitResolved::Instance(did, subst) =
                    TraitResolved::resolve_item(ctx.tcx, self.typing_env, item, substs)
            {
                t = ctx.normalize_erasing_regions(self.typing_env, Dependency::Item(did, subst))
            }

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
            Dependency::Type(_) => TyElab::expand(self, ctx, dep),
            Dependency::Item(def_id, subst) => {
                if ctx.is_logical(def_id) || matches!(ctx.item_type(def_id), ItemType::Constant) {
                    LogicElab::expand(self, ctx, dep)
                } else if matches!(ctx.def_kind(def_id), DefKind::Field | DefKind::Variant) {
                    self.namer(dep).ty(ctx.parent(def_id), subst);
                    vec![]
                } else {
                    ProgElab::expand(self, ctx, dep)
                }
            }
            Dependency::TyInvAxiom(ty) => expand_ty_inv_axiom(self, ctx, ty),
            Dependency::ClosureAccessor(_, _, _) => vec![],
            Dependency::Builtin(b) => {
                vec![Decl::UseDecls(Box::new([Use {
                    name: self.namer.prelude_module_name(b),
                    as_: None,
                    export: false,
                }]))]
            }
            Dependency::Eliminator(def_id, subst) => {
                vec![eliminator(ctx, &mut self.namer(dep), def_id, subst)]
            }
            Dependency::Promoted(_, _) => ProgElab::expand(self, ctx, dep),
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
    let (self_did, self_subst) = elab.self_key.did().unwrap();
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
    if is_trusted_function(ctx.tcx, self_did) || !ctx.has_body(self_did) {
        return;
    }

    for law in ctx.laws(item_container) {
        // We add a weak dep from `dep` to make sure it appears close to the triggering item
        elab.expansion_queue.push_back((dep, Strength::Weak, Dependency::Item(*law, item_subst)));
    }
}

fn val(mut sig: Signature, kind: DeclKind) -> Vec<Decl> {
    if let DeclKind::Predicate = kind {
        sig.retty = None;
    }
    sig.contract.variant = None;

    let ax = if !sig.contract.ensures.is_empty() { Some(spec_axiom(&sig)) } else { None };

    sig.contract = Default::default();

    let mut d = vec![Decl::LogicDecl(LogicDecl { kind: Some(kind), sig })];

    if !matches!(kind, DeclKind::Constant)
        && let Some(ax) = ax
    {
        d.push(Decl::Axiom(ax))
    }

    d
}

fn resolve_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let trait_meth_id = get_resolve_method(ctx.tcx);
    let sig = ctx.sig(def_id).clone();
    let mut pre_sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
    pre_sig = pre_sig.normalize(ctx.tcx, typing_env);

    let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);

    if let &TyKind::Closure(def_id, subst) = subst[0].as_type().unwrap().kind() {
        Some(closure_resolve(ctx, def_id, subst))
    } else {
        match traits::TraitResolved::resolve_item(ctx.tcx, typing_env, trait_meth_id, subst) {
            traits::TraitResolved::Instance(meth_did, meth_substs) => {
                // We know the instance => body points to it
                Some(Term::call(ctx.tcx, typing_env, meth_did, meth_substs, Box::new([arg])))
            }
            traits::TraitResolved::UnknownFound | traits::TraitResolved::UnknownNotFound => {
                // We don't know the instance => body is opaque
                None
            }
            traits::TraitResolved::NoInstance => {
                // We know there is no instance => body is true
                Some(Term::mk_true(ctx.tcx))
            }
        }
    }
}

fn fn_once_postcond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let tcx = ctx.tcx;
    let ty_self = subst.type_at(1);
    let self_ = Term::var(Symbol::intern("self"), ty_self);
    let args = Term::var(Symbol::intern("args"), subst.type_at(0));
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(get_fn_once_impl_postcond(tcx)).inputs[2].2),
    );
    let res = Term::var(Symbol::intern("result"), ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => ctx.closure_contract(*did).postcond_once.clone(),
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let args = Box::new([self_.clone().cur(), args, self_.fin(), res]);
            Some(Term::call(tcx, typing_env, get_fn_mut_impl_postcond(tcx), subst_postcond, args))
        }
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let args = Box::new([self_.coerce(*cl), args, res]);
            Some(Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, args))
        }
        _ => None,
    }
}

fn fn_mut_postcond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let tcx = ctx.tcx;
    let ty_self = subst.type_at(1);
    let self_ = Term::var(Symbol::intern("self"), ty_self);
    let args = Term::var(Symbol::intern("args"), subst.type_at(0));
    let result_state = Term::var(Symbol::intern("result_state"), ty_self);
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(get_fn_mut_impl_postcond(tcx)).inputs[3].2),
    );
    let res = Term::var(Symbol::intern("result"), ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => ctx.closure_contract(*did).postcond_mut.clone(),
        TyKind::Ref(_, cl, Mutability::Mut) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let args = Box::new([self_.clone().cur(), args, result_state.clone().cur(), res]);
            Some(
                Term::call(tcx, typing_env, get_fn_mut_impl_postcond(tcx), subst_postcond, args)
                    .conj(self_.fin().eq(ctx.tcx, result_state.fin())),
            )
        }
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let args = Box::new([self_.clone().coerce(*cl), args, res]);
            Some(
                Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, args)
                    .conj(self_.eq(ctx.tcx, result_state)),
            )
        }
        _ => None,
    }
}

fn fn_postcond_term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let tcx = ctx.tcx;
    let ty_self = subst.type_at(1);
    let self_ = Term::var(Symbol::intern("self"), ty_self);
    let args = Term::var(Symbol::intern("args"), subst.type_at(0));
    let ty_res = ctx.instantiate_and_normalize_erasing_regions(
        subst,
        typing_env,
        EarlyBinder::bind(ctx.sig(get_fn_impl_postcond(tcx)).inputs[2].2),
    );
    let res = Term::var(Symbol::intern("result"), ty_res);
    match ty_self.kind() {
        TyKind::Closure(did, _) => ctx.closure_contract(*did).postcond.clone(),
        TyKind::Ref(_, cl, Mutability::Not) => {
            let mut subst_postcond = subst.to_vec();
            subst_postcond[1] = GenericArg::from(*cl);
            let subst_postcond = ctx.mk_args(&subst_postcond);
            let args = Box::new([self_.clone().coerce(*cl), args, res]);
            Some(Term::call(tcx, typing_env, get_fn_impl_postcond(tcx), subst_postcond, args))
        }
        _ => None,
    }
}

// Returns a resolved and normalized term for a dependency.
// Currently, it does not handle invariant axioms but otherwise returns all logical terms.
fn term<'tcx>(
    ctx: &Why3Generator<'tcx>,
    typing_env: TypingEnv<'tcx>,
    dep: Dependency<'tcx>,
) -> Option<Term<'tcx>> {
    match dep {
        Dependency::Item(def_id, subst) => {
            if matches!(ctx.item_type(def_id), ItemType::Constant) {
                let ct = UnevaluatedConst::new(def_id, subst);
                let constant = Const::new(ctx.tcx, ConstKind::Unevaluated(ct));
                let ty = ctx.type_of(def_id).instantiate(ctx.tcx, subst);
                let ty = ctx.tcx.normalize_erasing_regions(typing_env, ty);
                let span = ctx.def_span(def_id);
                let res = from_ty_const(&ctx.ctx, constant, ty, typing_env, span);
                Some(res)
            } else if is_resolve_function(ctx.tcx, def_id) {
                resolve_term(ctx, typing_env, def_id, subst)
            } else if is_structural_resolve(ctx.tcx, def_id) {
                let subj = ctx.sig(def_id).inputs[0].0;
                structural_resolve(ctx, subj, subst.type_at(0))
            } else if is_fn_once_impl_postcond(ctx.tcx, def_id) {
                fn_once_postcond_term(ctx, typing_env, subst)
            } else if is_fn_mut_impl_postcond(ctx.tcx, def_id) {
                fn_mut_postcond_term(ctx, typing_env, subst)
            } else if is_fn_impl_postcond(ctx.tcx, def_id) {
                fn_postcond_term(ctx, typing_env, subst)
            } else if is_fn_once_impl_precond(ctx.tcx, def_id) {
                let TyKind::Closure(did, _) = subst.type_at(1).kind() else { return None };
                Some(ctx.closure_contract(*did).precond.clone())
            } else if is_fn_mut_impl_unnest(ctx.tcx, def_id) {
                let TyKind::Closure(did, _) = subst.type_at(1).kind() else { return None };
                Some(ctx.closure_contract(*did).unnest.clone().unwrap())
            } else {
                let term = ctx.term_fail_fast(def_id).unwrap().clone();
                let term = normalize(
                    ctx.tcx,
                    typing_env,
                    EarlyBinder::bind(term).instantiate(ctx.tcx, subst),
                );
                Some(term)
            }
        }
        _ => unreachable!(),
    }
}
