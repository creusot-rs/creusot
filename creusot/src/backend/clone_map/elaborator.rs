use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    backend::{
        is_trusted_function,
        logic::{lower_logical_defn, spec_axiom},
        program::{self},
        signature::named_sig_to_why3,
        structural_resolve::structural_resolve,
        term::lower_pure,
        ty::translate_ty,
        ty_inv::InvariantElaborator,
    },
    constant::from_ty_const,
    pearlite::{normalize, Term},
    traits,
};
use rustc_middle::ty::{self, Const, ParamEnv};
use rustc_span::DUMMY_SP;
use rustc_type_ir::EarlyBinder;
use util::{get_builtin, ident_of, PreSignature};
use why3::{
    declaration::{Axiom, Contract, LetKind, Signature, Use, ValDecl},
    exp::Binder,
};

use super::*;

/// The `Expander` takes a list of 'root' dependencies (items explicitly requested by user code),
/// and expands this into a complete dependency graph.
pub(super) struct Expander<'a, 'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, ()>,
    dep_bodies: HashMap<Dependency<'tcx>, Vec<Decl>>,
    namer: &'a mut CloneNames<'tcx>,
    self_key: Dependency<'tcx>,
    param_env: ParamEnv<'tcx>,
    expansion_queue: VecDeque<(Dependency<'tcx>, Dependency<'tcx>)>,
    tcx: TyCtxt<'tcx>,
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

    fn insert(&mut self, dep: Dependency<'tcx>) -> Kind {
        let dep = dep.erase_regions(self.namer.tcx);
        self.expansion_queue.push_back((self.source, dep));
        let k = self.namer.insert(dep);
        k
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
        let Some((def_id, subst)) = dep.did() else { return Vec::new() };

        let sig = ctx.sig(def_id).clone();
        let sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
        let sig = sig.normalize(ctx.tcx, elab.param_env);
        let sig = signature(ctx, elab, sig, dep);
        if util::is_ghost_closure(ctx.tcx, def_id) {
            // Inline the body of ghost closures
            let mut coma = program::to_why(
                ctx,
                &mut elab.namer(dep),
                BodyId { def_id: def_id.expect_local(), promoted: None },
            );
            coma.name = sig.name;
            return vec![Decl::Coma(coma)];
        };

        vec![program::val(ctx, sig)]
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

    let name = if let Dependency::ClosureSpec(_, _, _) = dep {
        names.insert(dep).ident()
    } else {
        names.insert(dep).ident()
    };

    let (def_id, _) = dep.did().unwrap();

    let sig = named_sig_to_why3(ctx, &mut names, name, &sig, def_id);
    sig
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
            Dependency::Item(_, _)
                | Dependency::TyInvAxiom(_)
                | Dependency::StructuralResolve(_)
                | Dependency::ClosureSpec(_, _, _)
        ));

        // TODO: Fold into `term`, but requires first some sort of
        // handling for axioms
        if let Dependency::TyInvAxiom(ty) = dep {
            return expand_ty_inv(elab, ctx, ty);
        }

        // TODO: getting rid of this requires breaking the dependency on `def_id` below.
        if let Dependency::StructuralResolve(ty) = dep {
            return expand_structural_resolve(elab, ctx, ty);
        }

        let Some((def_id, subst)) = dep.did() else { return Vec::new() };

        // This is the 'inv' symbol, which is defined using an axiom "TyInvAxiom".
        // We schedule this 'body' for expansion here by forcing it to be added to the expansion queue.
        if util::is_inv(ctx.tcx, def_id) {
            let ty = subst.type_at(0);
            let ty = ctx.try_normalize_erasing_regions(elab.param_env, ty).unwrap_or(ty);
            elab.expansion_queue.push_back((elab.self_key, Dependency::TyInvAxiom(ty)));
        }

        let kind = if dep.is_closure_spec() {
            let is_accessor =
                dep.to_trans_id(elab.tcx, elab.param_env).is_some_and(|i| ctx.is_accessor(i));
            if is_accessor {
                Some(LetKind::Function)
            } else {
                Some(LetKind::Predicate)
            }
        } else {
            util::item_type(ctx.tcx, def_id).let_kind()
        };

        if let Some(b) = get_builtin(ctx.tcx, def_id) {
            return vec![Decl::UseDecl(Use {
                name: QName::from_string(b.as_str()).module_qname(),
                as_: None,
                export: false,
            })];
        }

        let sig = sig(ctx, elab.param_env, dep);
        let mut sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
        sig = sig.normalize(ctx.tcx, elab.param_env);

        let trait_resol = ctx
            .tcx
            .trait_of_item(def_id)
            .map(|_| traits::resolve_assoc_item_opt(ctx.tcx, elab.param_env, def_id, subst));

        let is_opaque = matches!(
            trait_resol,
            Some(traits::TraitResol::UnknownFound | traits::TraitResol::UnknownNotFound)
        ) || elab
            .self_key
            .did()
            .is_some_and(|(self_did, _)| !ctx.is_transparent_from(def_id, self_did));

        if is_opaque {
            let mut sig = signature(ctx, elab, sig, dep);
            if let Some(LetKind::Predicate) = kind {
                sig.retty = None;
            }
            val(ctx, sig, kind)
        } else {
            let sig = signature(ctx, elab, sig, dep);

            let Some(term) = term(ctx, elab.param_env, dep) else { return val(ctx, sig, kind) };

            lower_logical_defn(ctx, &mut elab.namer(dep), sig, kind, term)
        }
    }
}

// TODO Deprecate and fold into LogicElab
fn expand_ty_inv<'tcx>(
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

// TODO Deprecate and fold into LogicElab
fn expand_structural_resolve<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let (binder, term) = structural_resolve(ctx, ty);
    let param_env = elab.param_env;
    let mut names = elab.namer(Dependency::StructuralResolve(ty));
    let exp = if let Some(mut term) = term {
        normalize(ctx.tcx, param_env, &mut term);
        Some(lower_pure(ctx, &mut names, &term))
    } else {
        None
    };

    let binder =
        Binder::typed(ident_of(binder.0), translate_ty(ctx, &mut names, DUMMY_SP, binder.1));
    let sig = Signature {
        name: names.insert(Dependency::StructuralResolve(ty)).ident(),
        trigger: None,
        attrs: vec![],
        retty: None,
        args: vec![binder],
        contract: Contract::default(),
    };

    let pred = Decl::predicate(sig, exp);

    vec![pred]
}

pub fn resolve_term<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Option<Term<'tcx>> {
    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
    let sig = ctx.sig(def_id).clone();
    let mut pre_sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
    pre_sig = pre_sig.normalize(ctx.tcx, param_env);

    let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);
    let body;

    if let TyKind::Closure(..) = subst[0].as_type().unwrap().kind() {
        // Closures have an "hacked" instance of Resolve
        body = Term::call(ctx.tcx, trait_meth_id, subst, vec![arg]);
    } else {
        match traits::resolve_assoc_item_opt(ctx.tcx, param_env, trait_meth_id, subst) {
            traits::TraitResol::Instance(meth_did, meth_substs) => {
                // We know the instance => body points to it
                body = Term::call(ctx.tcx, meth_did, meth_substs, vec![arg]);
            }
            traits::TraitResol::UnknownFound | traits::TraitResol::UnknownNotFound => {
                // We don't know the instance => body is opaque
                return None;
            }
            traits::TraitResol::NoInstance => {
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
        assert!(matches!(dep, Dependency::Type(_)));

        let Dependency::Type(ty) = dep else { return Vec::new() };
        let Some((def_id, subst)) = dep.did() else { return Vec::new() };

        let mut names = elab.namer(dep);
        match ty.kind() {
            TyKind::Alias(_, _) => vec![ctx.assoc_ty_decl(&mut names, def_id, subst)],
            _ => {
                if let Some(why3_modl) = util::get_builtin(ctx.tcx, def_id) {
                    let qname = QName::from_string(why3_modl.as_str());
                    let Kind::Used(_, _) = names.insert(Dependency::Type(ty)) else {
                        return vec![];
                    };

                    let use_decl = Use { as_: None, name: qname.module_qname(), export: false };

                    vec![Decl::UseDecl(use_decl)]
                } else {
                    let name = names.insert(dep).qname();

                    let modl = if util::item_type(ctx.tcx, def_id) == ItemType::Closure {
                        ctx.module_path_with_suffix(def_id, "_Type")
                    } else {
                        ctx.module_path(def_id)
                    };
                    let name = if name.module.is_empty() { name } else { name.module_qname() };
                    let use_decl = Use { as_: Some(name.as_ident()), name: modl, export: false };
                    vec![Decl::UseDecl(use_decl)]
                }
            }
        }
    }
}

impl<'a, 'tcx> Expander<'a, 'tcx> {
    pub fn new(
        namer: &'a mut CloneNames<'tcx>,
        self_key: Dependency<'tcx>,
        param_env: ParamEnv<'tcx>,
        tcx: TyCtxt<'tcx>,
        initial: impl Iterator<Item = Dependency<'tcx>>,
    ) -> Self {
        let exp = Self {
            graph: Default::default(),

            namer,
            self_key,
            param_env,
            expansion_queue: initial.map(|b| (self_key, b)).collect(),
            tcx,
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
        while let Some((s, t)) = self.expansion_queue.pop_front() {
            let t = t.resolve(ctx.tcx, self.param_env).unwrap_or(t);

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
            Dependency::Item(mut def_id, _) => {
                if ctx.is_logical(def_id) {
                    LogicElab::expand(self, ctx, dep)
                } else if ctx.is_constant(dep.to_trans_id(ctx.tcx, self.param_env).unwrap()) {
                    LogicElab::expand(self, ctx, dep)
                } else if matches!(ctx.def_kind(def_id), DefKind::Field) {
                    if util::item_type(self.tcx, def_id) == ItemType::Field {
                        def_id = self.tcx.parent(def_id);
                    };
                    let name = self.namer.insert(dep).qname();
                    let modl = ctx.module_path(def_id);
                    let name = if name.module.is_empty() { name } else { name.module_qname() };
                    let use_decl = Use {
                        as_: Some(Ident::from_string(name.to_string())),
                        name: modl,
                        export: false,
                    };
                    vec![Decl::UseDecl(use_decl)]
                } else {
                    ProgElab::expand(self, ctx, dep)
                }
            }
            Dependency::TyInvAxiom(_) => LogicElab::expand(self, ctx, dep),
            Dependency::StructuralResolve(_) => LogicElab::expand(self, ctx, dep),
            Dependency::ClosureSpec(_, _, _) => LogicElab::expand(self, ctx, dep),
            Dependency::Builtin(b) => {
                vec![Decl::UseDecl(Use { name: b.qname(), as_: None, export: false })]
            }
        };

        self.dep_bodies.insert(dep, decls);
    }
}

fn expand_laws<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    dep: Dependency<'tcx>,
) {
    let Some((self_did, _)) = elab.self_key.did() else {
        return;
    };
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
    if is_trusted_function(ctx.tcx, self_did) || !util::has_body(ctx, self_did) {
        return;
    }

    let tcx = ctx.tcx;
    let mut namer = elab.namer(elab.self_key);
    for law in ctx.laws(item.container_id(tcx)) {
        let dep = Dependency::new(tcx, (*law, item_subst));

        namer.insert(dep);
    }
}

pub fn val<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    mut sig: Signature,
    kind: Option<LetKind>,
) -> Vec<Decl> {
    sig.contract.variant = Vec::new();
    if let Some(k) = kind {
        let ax = if !sig.contract.is_empty() { Some(spec_axiom(&sig)) } else { None };

        sig.contract = Default::default();
        if let LetKind::Predicate = k {
            sig.retty = None;
        };

        if let LetKind::Constant = k {
            return vec![Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig })];
        }

        let mut d = vec![Decl::ValDecl(ValDecl { ghost: false, val: false, kind, sig })];

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
    let trans_id = dep.to_trans_id(ctx.tcx, param_env)?;
    match dep {
        Dependency::Item(def_id, subst) => {
            if ctx.is_constant(trans_id) {
                let uneval = ty::UnevaluatedConst::new(def_id, subst);
                let constant = Const::new(ctx.tcx, ty::ConstKind::Unevaluated(uneval));
                let ty = ctx.type_of(def_id).instantiate(ctx.tcx, subst);
                let span = ctx.def_span(def_id);
                let res = from_ty_const(&mut ctx.ctx, constant, ty, param_env, span);
                Some(res)
            } else if util::is_resolve_function(ctx.tcx, def_id) {
                resolve_term(ctx, param_env, def_id, subst)
            } else {
                let term = ctx.term(trans_id).cloned()?;
                let mut term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
                normalize(ctx.tcx, param_env, &mut term);

                Some(term)
            }
        }
        Dependency::StructuralResolve(ty) => {
            let (_, term) = structural_resolve(ctx, ty);
            term
        }
        _ => ctx.term(trans_id).cloned(),
    }
}

// Builds a presignature for a dependency, does not yet handle structural resolve or invariant axioms
// In the future, we should change this to also store the function name and simplify upstream
// code further.
pub fn sig<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    param_env: ParamEnv<'tcx>,
    dep: Dependency<'tcx>,
) -> PreSignature<'tcx> {
    match dep.to_trans_id(ctx.tcx, param_env).unwrap() {
        TransId::Item(id) => ctx.sig(id).clone(),

        TransId::Hacked(h_id, id) => match h_id {
            ClosureSpecKind::PostconditionOnce => {
                ctx.closure_contract(id).postcond_once.as_ref().unwrap().0.clone()
            }
            ClosureSpecKind::PostconditionMut => {
                ctx.closure_contract(id).postcond_mut.as_ref().unwrap().0.clone()
            }
            ClosureSpecKind::Postcondition => {
                ctx.closure_contract(id).postcond.as_ref().unwrap().0.clone()
            }
            ClosureSpecKind::Precondition => ctx.closure_contract(id).precond.0.clone(),
            ClosureSpecKind::Unnest => ctx.closure_contract(id).unnest.as_ref().unwrap().0.clone(),
            ClosureSpecKind::Resolve => ctx.closure_contract(id).resolve.0.clone(),
            ClosureSpecKind::Accessor(ix) => {
                ctx.closure_contract(id).accessors[ix as usize].0.clone()
            }
        },
        // In future change this
        TransId::TyInvAxiom(_) | TransId::StructuralResolve(_) => unreachable!(),
    }
}
