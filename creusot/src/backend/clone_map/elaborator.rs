use std::{
    collections::{HashMap, HashSet, VecDeque},
    iter,
};

use crate::{
    backend::{
        clone_map::{CloneNames, Dependency, Kind},
        dependency::ClosureSpecKind,
        is_trusted_function,
        logic::{lower_logical_defn, spec_axiom},
        program,
        signature::sig_to_why3,
        structural_resolve::structural_resolve,
        term::lower_pure,
        ty::{eliminator, translate_closure_ty, translate_ty, translate_tydecl},
        ty_inv::InvariantElaborator,
        Namer, TranslationCtx, Why3Generator,
    },
    constant::from_ty_const,
    contracts_items::{
        get_builtin, get_resolve_method, is_inv_function, is_resolve_function,
        is_structural_resolve,
    },
    ctx::{BodyId, ItemType},
    pearlite::{normalize, Term},
    specification::PreSignature,
    traits::{self, TraitResolved},
};
use petgraph::graphmap::DiGraphMap;
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_middle::ty::{
    Const, ConstKind, GenericArgsRef, ParamEnv, Ty, TyCtxt, TyKind, TypeFoldable, UnevaluatedConst,
};
use rustc_span::{Span, DUMMY_SP};
use rustc_type_ir::EarlyBinder;
use why3::{
    declaration::{Axiom, Decl, DeclKind, LogicDecl, Signature, TyDecl, Use},
    QName,
};

/// The `Expander` takes a list of 'root' dependencies (items explicitly requested by user code),
/// and expands this into a complete dependency graph.
pub(super) struct Expander<'a, 'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, ()>,
    dep_bodies: HashMap<Dependency<'tcx>, Vec<Decl>>,
    namer: &'a mut CloneNames<'tcx>,
    self_key: Dependency<'tcx>,
    param_env: ParamEnv<'tcx>,
    expansion_queue: VecDeque<(Dependency<'tcx>, Dependency<'tcx>)>,
}

struct ExpansionProxy<'a, 'tcx> {
    namer: &'a mut CloneNames<'tcx>,
    expansion_queue: &'a mut VecDeque<(Dependency<'tcx>, Dependency<'tcx>)>,
    source: Dependency<'tcx>,
}

impl<'a, 'tcx> Namer<'tcx> for ExpansionProxy<'a, 'tcx> {
    fn normalize<T: TypeFoldable<TyCtxt<'tcx>> + Copy>(
        &self,
        ctx: &TranslationCtx<'tcx>,
        ty: T,
    ) -> T {
        self.namer.normalize(ctx, ty)
    }

    fn insert(&mut self, dep: Dependency<'tcx>) -> &Kind {
        let dep = dep.erase_regions(self.tcx());
        self.expansion_queue.push_back((self.source, dep));
        self.namer.insert(dep)
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.namer.tcx()
    }

    fn span(&mut self, span: Span) -> Option<why3::declaration::Attribute> {
        self.namer.span(span)
    }
}

trait DepElab {
    // type Sig;
    // type Contract;
    // type Body;

    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<why3::declaration::Decl>;
}

struct ProgElab;

impl DepElab for ProgElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<why3::declaration::Decl> {
        if let Dependency::Item(def_id, subst) = dep
            && ctx.def_kind(def_id) != DefKind::Closure
        {
            let sig = ctx.sig(def_id).clone();
            let sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
            let sig = sig.normalize(ctx.tcx, elab.param_env);
            let sig = signature(ctx, elab, sig, dep);
            return vec![program::val(ctx, sig)];
        }

        // Inline the body of closures and promoted
        let mut names = elab.namer(dep);
        let name = names.insert(dep).ident();

        let bid = match dep {
            Dependency::Item(def_id, _) => BodyId { def_id: def_id.expect_local(), promoted: None },
            Dependency::Promoted(def_id, prom) => BodyId { def_id, promoted: Some(prom) },
            _ => unreachable!(),
        };

        let coma = program::to_why(ctx, &mut names, name, bid);
        return vec![Decl::Coma(coma)];
    }
}

// What is the difference with `sig` below and `sigs` in logic?
fn signature<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    elab: &mut Expander<'_, 'tcx>,
    sig: PreSignature<'tcx>,
    dep: Dependency<'tcx>,
) -> Signature {
    let mut names = elab.namer(dep);
    let name = names.insert(dep).ident();
    let (def_id, _) = dep.did().unwrap();
    sig_to_why3(ctx, &mut names, name, sig, def_id)
}

struct LogicElab;

// TODO refactor1!!!1
//
// The main thrust of refactorings would be to unify the different ways
// we generate logical definitions, ideally, we should only have one way to
// turn a Pearlite term into a Why3 declaration.
// Currently, we have specialcasing for invariant axioms and other various bits-and-bobs.
impl DepElab for LogicElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<why3::declaration::Decl> {
        assert!(matches!(
            dep,
            Dependency::Item(_, _) | Dependency::TyInvAxiom(_) | Dependency::ClosureSpec(_, _, _)
        ));

        // TODO: Fold into `term`, but requires first some sort of
        // handling for axioms
        if let Dependency::TyInvAxiom(ty) = dep {
            return expand_ty_inv_axiom(elab, ctx, ty);
        }

        let (def_id, subst) = dep.did().unwrap();

        if is_inv_function(ctx.tcx, def_id) {
            elab.expansion_queue
                .push_back((Dependency::AllTyInvAxioms, Dependency::TyInvAxiom(subst.type_at(0))));
        }

        let kind = if dep.is_closure_spec() {
            Some(DeclKind::Predicate)
        } else {
            match ctx.item_type(def_id) {
                ItemType::Logic { .. } => Some(DeclKind::Function),
                ItemType::Predicate { .. } => Some(DeclKind::Predicate),
                ItemType::Program | ItemType::Closure => None,
                ItemType::Constant => Some(DeclKind::Constant),
                _ => None,
            }
        };

        if let Some(b) = get_builtin(ctx.tcx, def_id) {
            let Some(name) = QName::from_string(b.as_str()).module_qname() else { return vec![] };
            return vec![Decl::UseDecl(Use { name, as_: None, export: false })];
        }

        let sig = sig(ctx, dep);
        let mut sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
        sig = sig.normalize(ctx.tcx, elab.param_env);

        let trait_resol = ctx
            .tcx
            .trait_of_item(def_id)
            .map(|_| traits::TraitResolved::resolve_item(ctx.tcx, elab.param_env, def_id, subst));

        let is_opaque = matches!(
            trait_resol,
            Some(traits::TraitResolved::UnknownFound | traits::TraitResolved::UnknownNotFound)
        ) || !ctx.is_transparent_from(def_id, elab.self_key.did().unwrap().0)
            || is_trusted_function(ctx.tcx, def_id);

        let mut sig = signature(ctx, elab, sig, dep);
        if !is_opaque && let Some(term) = term(ctx, elab.param_env, dep) {
            lower_logical_defn(ctx, &mut elab.namer(dep), sig, kind, term)
        } else {
            if let Some(DeclKind::Predicate) = kind {
                sig.retty = None;
            }
            val(ctx, sig, kind)
        }
    }
}

// TODO Deprecate and fold into LogicElab
fn expand_ty_inv_axiom<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let param_env = elab.param_env;
    let mut names = elab.namer(Dependency::TyInvAxiom(ty));

    let mut elab = InvariantElaborator::new(param_env, ctx);
    let Some(term) = elab.elaborate_inv(ty, false) else { return vec![] };
    let rewrite = elab.rewrite;
    let exp = lower_pure(ctx, &mut names, &term);
    let axiom =
        Axiom { name: names.insert(Dependency::TyInvAxiom(ty)).qname().name, rewrite, axiom: exp };
    vec![Decl::Axiom(axiom)]
}

pub fn resolve_term<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let trait_meth_id = get_resolve_method(ctx.tcx);
    let sig = ctx.sig(def_id).clone();
    let mut pre_sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
    pre_sig = pre_sig.normalize(ctx.tcx, param_env);

    let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);
    let body;

    if let TyKind::Closure(..) = subst[0].as_type().unwrap().kind() {
        // Closures have an "hacked" instance of Resolve
        body = Term::call(ctx.tcx, param_env, trait_meth_id, subst, vec![arg]);
    } else {
        match traits::TraitResolved::resolve_item(ctx.tcx, param_env, trait_meth_id, subst) {
            traits::TraitResolved::Instance(meth_did, meth_substs) => {
                // We know the instance => body points to it
                body = Term::call(ctx.tcx, param_env, meth_did, meth_substs, vec![arg]);
            }
            traits::TraitResolved::UnknownFound | traits::TraitResolved::UnknownNotFound => {
                // We don't know the instance => body is opaque
                return None;
            }
            traits::TraitResolved::NoInstance => {
                // We know there is no instance => body is true
                body = Term::mk_true(ctx.tcx);
            }
        }
    }
    Some(body)
}

struct TyElab;

impl DepElab for TyElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
    ) -> Vec<why3::declaration::Decl> {
        let Dependency::Type(ty) = dep else { unreachable!() };
        let param_env = elab.param_env;
        let mut names = elab.namer(dep);
        match ty.kind() {
            TyKind::Param(_) => vec![Decl::TyDecl(TyDecl::Opaque {
                ty_name: names.ty_param(ty).as_ident(),
                ty_params: vec![],
            })],
            TyKind::Alias(_, _) => {
                let (def_id, subst) = dep.did().unwrap();
                assert_eq!(
                    ctx.tcx.associated_item(def_id).container,
                    rustc_middle::ty::TraitContainer
                );
                vec![Decl::TyDecl(TyDecl::Opaque {
                    ty_name: names.ty(def_id, subst).as_ident(),
                    ty_params: vec![],
                })]
            }
            TyKind::Closure(did, subst) => translate_closure_ty(ctx, &mut names, *did, subst)
                .map_or(vec![], |d| vec![Decl::TyDecl(d)]),
            TyKind::Adt(adt_def, subst)
                if let Some(why3_modl) = get_builtin(ctx.tcx, adt_def.did()) =>
            {
                assert!(matches!(names.insert(dep), Kind::UsedBuiltin(_, _)));

                for ty in subst.types() {
                    translate_ty(ctx, &mut elab.namer(dep), DUMMY_SP, ty);
                }

                let qname = QName::from_string(why3_modl.as_str());
                let Some(name) = qname.module_qname() else { return vec![] };
                let use_decl = Use { as_: None, name, export: false };
                vec![Decl::UseDecl(use_decl)]
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
        param_env: ParamEnv<'tcx>,
        initial: impl Iterator<Item = Dependency<'tcx>>,
    ) -> Self {
        let exp = Self {
            graph: Default::default(),
            namer,
            self_key,
            param_env,
            expansion_queue: initial
                .chain(iter::once(Dependency::AllTyInvAxioms))
                .map(|b| (self_key, b))
                .collect(),
            dep_bodies: Default::default(),
        };
        exp
    }

    fn namer(&mut self, source: Dependency<'tcx>) -> ExpansionProxy<'_, 'tcx> {
        ExpansionProxy {
            namer: &mut self.namer,
            expansion_queue: &mut self.expansion_queue,
            source,
        }
    }

    /// Expand the graph with new entries
    pub fn update_graph(
        mut self,
        ctx: &mut Why3Generator<'tcx>,
    ) -> (DiGraphMap<Dependency<'tcx>, ()>, HashMap<Dependency<'tcx>, Vec<Decl>>) {
        let mut visited = HashSet::new();
        while let Some((s, mut t)) = self.expansion_queue.pop_front() {
            if let Dependency::Item(item, substs) = t
                && ctx.trait_of_item(item).is_some()
                && let TraitResolved::Instance(did, subst) =
                    TraitResolved::resolve_item(ctx.tcx, self.param_env, item, substs)
            {
                t = ctx.normalize_erasing_regions(
                    self.param_env,
                    Dependency::item(ctx.tcx, (did, subst)),
                )
            }
            self.graph.add_edge(s, t, ());

            if !visited.insert(t) {
                continue;
            }
            self.expand(ctx, t);
        }

        (self.graph, self.dep_bodies)
    }

    fn expand(&mut self, ctx: &mut Why3Generator<'tcx>, dep: Dependency<'tcx>) {
        expand_laws(self, ctx, dep);

        let decls = match dep {
            Dependency::Type(_) => TyElab::expand(self, ctx, dep),
            Dependency::Item(def_id, subst) => {
                if ctx.is_logical(def_id) || matches!(ctx.item_type(def_id), ItemType::Constant) {
                    LogicElab::expand(self, ctx, dep)
                } else if matches!(ctx.def_kind(def_id), DefKind::Field | DefKind::Variant) {
                    let mut namer = self.namer(dep);
                    namer.ty(ctx.parent(def_id), subst);
                    vec![]
                } else {
                    ProgElab::expand(self, ctx, dep)
                }
            }
            Dependency::TyInvAxiom(_) => LogicElab::expand(self, ctx, dep),
            Dependency::ClosureSpec(ClosureSpecKind::Accessor(_), _, _) => vec![],
            Dependency::ClosureSpec(_, _, _) => LogicElab::expand(self, ctx, dep),
            Dependency::Builtin(b) => {
                vec![Decl::UseDecl(Use { name: b.qname(), as_: None, export: false })]
            }
            Dependency::Eliminator(def_id, subst) => {
                vec![eliminator(ctx, &mut self.namer(dep), def_id, subst)]
            }
            Dependency::Promoted(_, _) => ProgElab::expand(self, ctx, dep),
            Dependency::AllTyInvAxioms => vec![],
        };

        // Make every declaration that creates a goal depend on every TyInvAxiom to make sure that
        // TyInvAxioms are visible at this point
        if decls.iter().any(|d| matches!(d, Decl::Coma(..) | Decl::Goal(_))) {
            self.expansion_queue.push_back((dep, Dependency::AllTyInvAxioms));
        }

        self.dep_bodies.insert(dep, decls);
    }
}

fn expand_laws<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    dep: Dependency<'tcx>,
) {
    let (self_did, _) = elab.self_key.did().unwrap();
    let Some((item_did, item_subst)) = dep.did() else {
        return;
    };

    let Some(item) = ctx.opt_associated_item(item_did) else { return };

    // Dont clone laws into the trait / impl which defines them.
    if let Some(self_item) = ctx.opt_associated_item(self_did)
        && self_item.container_id(ctx.tcx) == item.container_id(ctx.tcx)
    {
        return;
    }

    // TODO: Push out of graph expansion
    // If the function we are cloning into is `#[trusted]` there is no need for laws.
    // Similarily, if it has no body, there will be no proofs.
    if is_trusted_function(ctx.tcx, self_did) || !ctx.has_body(self_did) {
        return;
    }

    let tcx = ctx.tcx;
    let mut namer = elab.namer(elab.self_key);
    for law in ctx.laws(item.container_id(tcx)) {
        namer.insert(Dependency::item(tcx, (*law, item_subst)));
    }
}

pub fn val<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    mut sig: Signature,
    kind: Option<DeclKind>,
) -> Vec<Decl> {
    sig.contract.variant = Vec::new();
    if let Some(k) = kind {
        let ax = if !sig.contract.is_empty() { Some(spec_axiom(&sig)) } else { None };

        sig.contract = Default::default();
        if let DeclKind::Predicate = k {
            sig.retty = None;
        };

        if let DeclKind::Constant = k {
            return vec![Decl::LogicDecl(LogicDecl { kind, sig })];
        }

        let mut d = vec![Decl::LogicDecl(LogicDecl { kind, sig })];

        if let Some(ax) = ax {
            d.push(Decl::Axiom(ax))
        }
        d
    } else {
        vec![program::val(ctx, sig)]
    }
}

// Returns a resolved and normalized term for a dependency.
// Currently, it does not handle invariant axioms but otherwise returns all logical terms.
pub fn term<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    dep: Dependency<'tcx>,
) -> Option<Term<'tcx>> {
    match dep {
        Dependency::Item(def_id, subst) => {
            if matches!(ctx.item_type(def_id), ItemType::Constant) {
                let uneval = UnevaluatedConst::new(def_id, subst);
                let constant = Const::new(ctx.tcx, ConstKind::Unevaluated(uneval));
                let ty = ctx.type_of(def_id).instantiate(ctx.tcx, subst);
                let ty = ctx.tcx.normalize_erasing_regions(param_env, ty);
                let span = ctx.def_span(def_id);
                let res = from_ty_const(&mut ctx.ctx, constant, ty, param_env, span);
                Some(res)
            } else if is_resolve_function(ctx.tcx, def_id) {
                resolve_term(ctx, param_env, def_id, subst)
            } else if is_structural_resolve(ctx.tcx, def_id) {
                let sig = ctx.sig(def_id).clone();
                structural_resolve(ctx, sig.inputs[0].0, subst.type_at(0))
            } else {
                let term = ctx.ctx.term(def_id).unwrap().clone();
                let term = normalize(
                    ctx.tcx,
                    param_env,
                    EarlyBinder::bind(term).instantiate(ctx.tcx, subst),
                );
                Some(term)
            }
        }
        Dependency::ClosureSpec(cs, did, _) => {
            let c = ctx.ctx.closure_contract(did);
            match cs {
                ClosureSpecKind::PostconditionOnce => {
                    Some(c.postcond_once.as_ref().unwrap().1.clone())
                }
                ClosureSpecKind::PostconditionMut => {
                    Some(c.postcond_mut.as_ref().unwrap().1.clone())
                }
                ClosureSpecKind::Postcondition => Some(c.postcond.as_ref().unwrap().1.clone()),
                ClosureSpecKind::Precondition => Some(c.precond.1.clone()),
                ClosureSpecKind::Unnest => Some(c.unnest.as_ref().unwrap().1.clone()),
                ClosureSpecKind::Resolve => Some(c.resolve.1.clone()),
                ClosureSpecKind::Accessor(_) => unreachable!(),
            }
        }
        _ => unreachable!(),
    }
}

// Builds a presignature for a dependency, does not yet handle structural resolve or invariant axioms
// In the future, we should change this to also store the function name and simplify upstream
// code further.
pub fn sig<'tcx>(ctx: &mut Why3Generator<'tcx>, dep: Dependency<'tcx>) -> PreSignature<'tcx> {
    match dep {
        Dependency::Item(def_id, _) => ctx.sig(def_id).clone(),
        Dependency::ClosureSpec(ClosureSpecKind::PostconditionOnce, def_id, _) => {
            ctx.closure_contract(def_id).postcond_once.as_ref().unwrap().0.clone()
        }
        Dependency::ClosureSpec(ClosureSpecKind::PostconditionMut, def_id, _) => {
            ctx.closure_contract(def_id).postcond_mut.as_ref().unwrap().0.clone()
        }
        Dependency::ClosureSpec(ClosureSpecKind::Postcondition, def_id, _) => {
            ctx.closure_contract(def_id).postcond.as_ref().unwrap().0.clone()
        }
        Dependency::ClosureSpec(ClosureSpecKind::Precondition, def_id, _) => {
            ctx.closure_contract(def_id).precond.0.clone()
        }
        Dependency::ClosureSpec(ClosureSpecKind::Unnest, def_id, _) => {
            ctx.closure_contract(def_id).unnest.as_ref().unwrap().0.clone()
        }
        Dependency::ClosureSpec(ClosureSpecKind::Resolve, def_id, _) => {
            ctx.closure_contract(def_id).resolve.0.clone()
        }
        _ => unreachable!(),
    }
}
