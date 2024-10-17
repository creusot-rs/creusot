use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    backend::{
        is_trusted_function,
        logic::{lower_logical_defn, lower_pure_defn, sigs, spec_axiom},
        program::{self},
        signature::named_sig_to_why3,
        structural_resolve::structural_resolve,
        term::lower_pure,
        ty::translate_ty,
        ty_inv::InvariantElaborator,
    },
    pearlite::{normalize, Term},
    specification::PreContract,
    traits,
};
use rustc_middle::ty::{self, Const, ParamEnv};
use rustc_span::DUMMY_SP;
use rustc_type_ir::EarlyBinder;
use util::{get_builtin, ident_of, PreSignature};
use why3::{
    declaration::{Axiom, Constant, Contract, LetKind, Signature, Use, ValDecl},
    exp::Binder,
};

use super::*;

/// The `Expander` takes a list of 'root' dependencies (items explicitly requested by user code),
/// and expands this into a complete dependency graph.
pub(super) struct Expander<'a, 'tcx> {
    graph: DiGraphMap<Dependency<'tcx>, ()>,
    dep_bodies: HashMap<Dependency<'tcx>, Vec<Decl>>,
    dep_level: HashMap<Dependency<'tcx>, CloneLevel>,
    namer: &'a mut CloneNames<'tcx>,
    self_key: Dependency<'tcx>,
    param_env: ParamEnv<'tcx>,
    expansion_queue: VecDeque<(Dependency<'tcx>, CloneLevel, Dependency<'tcx>)>,
    tcx: TyCtxt<'tcx>,
}

// #[derive(Default)]
// pub struct DepBody {
//     pub sig: Option<Signature>,
//     pub contract: Option<Contract>,
//     pub body: Option<()>,
// }

struct ExpansionProxy<'a, 'tcx> {
    namer: &'a mut CloneNames<'tcx>,
    expansion_queue: &'a mut VecDeque<(Dependency<'tcx>, CloneLevel, Dependency<'tcx>)>,
    level: CloneLevel,
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

    fn with_vis<F, A>(&mut self, vis: CloneLevel, f: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        f(self)
    }

    fn insert(&mut self, dep: Dependency<'tcx>) -> Kind {
        // TODO Get accurate level
        self.expansion_queue.push_back((self.source, self.level, dep));
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
        level: CloneLevel,
    ) -> Vec<why3::declaration::Decl>;
}

struct ProgElab;

impl DepElab for ProgElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
        level: CloneLevel,
    ) -> Vec<why3::declaration::Decl> {
        let Some((def_id, subst)) = dep.did() else { return Vec::new() };

        let sig = ctx.sig(def_id).clone();
        let sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
        let sig = sig.normalize(ctx.tcx, elab.param_env);

        let sig = signature(ctx, elab, sig, dep, level);
        vec![program::val(ctx, sig)]
    }
}

fn signature<'tcx>(
    ctx: &mut Why3Generator<'tcx>,
    elab: &mut Expander<'_, 'tcx>,
    sig: PreSignature<'tcx>,
    dep: Dependency<'tcx>,
    level: CloneLevel,
) -> Signature {
    let mut names = elab.namer(level, dep);

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

impl DepElab for LogicElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
        mut level: CloneLevel,
    ) -> Vec<why3::declaration::Decl> {
        assert!(matches!(
            dep,
            Dependency::Item(_, _)
                | Dependency::TyInvAxiom(_)
                | Dependency::StructuralResolve(_)
                | Dependency::ClosureSpec(_, _, _)
        ));

        if let Dependency::TyInvAxiom(ty) = dep {
            return expand_ty_inv(elab, ctx, ty);
        }

        if let Dependency::StructuralResolve(ty) = dep {
            return expand_structural_resolve(elab, ctx, ty);
        }

        let Some((def_id, subst)) = dep.did() else { return Vec::new() };

        let is_accessor =
            dep.to_trans_id(elab.tcx, elab.param_env).is_some_and(|i| ctx.is_accessor(i));
        let kind = if dep.is_closure_spec() {
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

        if util::is_resolve_function(ctx.tcx, def_id) {
            let decls = expand_resolve_func(elab, ctx, def_id, subst);
            return decls;
        }

        if util::is_inv(ctx.tcx, def_id) {
            let ty = subst.type_at(0);
            let ty = ctx.try_normalize_erasing_regions(elab.param_env, ty).unwrap_or(ty);
            elab.expansion_queue.push_back((
                elab.self_key,
                CloneLevel::Body,
                Dependency::TyInvAxiom(ty),
            ));
            elab.graph.add_edge(Dependency::TyInvAxiom(ty), dep, ());
            let sig = signature(ctx, elab, sig, dep, level);

            return val(ctx, sig, kind);
        }

        // eprintln!("{dep:?} :- {level:?}");

        if elab
            .self_key
            .did()
            .is_some_and(|(self_did, _)| !ctx.is_transparent_from(def_id, self_did))
        {
            // eprintln!("{dep:?}");
            level = level.min(CloneLevel::Contract);
        };

        match level {
            CloneLevel::Signature => {
                sig.contract = PreContract::default();
                let sig = signature(ctx, elab, sig, dep, level);
                val(ctx, sig, kind)
            }
            CloneLevel::Contract => {
                let mut sig = signature(ctx, elab, sig, dep, level);
                if let Some(LetKind::Predicate) = kind {
                    sig.retty = None;
                }
                val(ctx, sig, kind)
            }
            CloneLevel::Body => {
                let sig = signature(ctx, elab, sig, dep, level);
                // sig.contract = Contract::default();

                if ctx.is_constant(def_id) {
                    let uneval = ty::UnevaluatedConst::new(def_id, subst);
                    let constant = Const::new(ctx.tcx, ty::ConstKind::Unevaluated(uneval));
                    let ty = ctx.type_of(def_id).instantiate_identity();

                    let span = ctx.def_span(def_id);
                    let res = crate::constant::from_ty_const(
                        &mut ctx.ctx,
                        constant,
                        ty,
                        elab.param_env,
                        span,
                    );

                    let res = lower_pure(ctx, &mut elab.namer(level, dep), &res);
                    return vec![Decl::ConstantDecl(Constant {
                        type_: sig.retty.unwrap(),
                        name: sig.name,
                        body: Some(res),
                    })];
                };

                let Some(term) = term(ctx, elab.param_env, dep) else { return val(ctx, sig, kind) };

                let mut term = EarlyBinder::bind(term).instantiate(ctx.tcx, subst);
                normalize(ctx.tcx, elab.param_env, &mut term);
                // eprintln!("{term:?}");
                if is_accessor {
                    lower_logical_defn(ctx, &mut elab.namer(level, dep), sig, kind, term)
                } else if dep.is_closure_spec() {
                    // TODO: Clean this up and merge with previous branches
                    lower_pure_defn(ctx, &mut elab.namer(level, dep), sig, kind, false, term)
                } else {
                    lower_logical_defn(ctx, &mut elab.namer(level, dep), sig, kind, term)
                }
            }
            CloneLevel::Root => unreachable!(),
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
    let mut names = elab.namer(CloneLevel::Body, Dependency::TyInvAxiom(ty));

    // eprintln!("{:?}", names.insert( Dependency::TyInvAxiom(ty)));
    let mut elab = InvariantElaborator::new(param_env, ctx);
    if let Some(term) = elab.elaborate_inv(ty, false) {
        let rewrite = elab.rewrite;
        let exp = lower_pure(ctx, &mut names, &term);
        let axiom = Axiom { name: names.ty_inv(ty).name, rewrite, axiom: exp };
        vec![Decl::Axiom(axiom)]
    } else {
        vec![]
    }
}

// TODO Deprecate and fold into LogicElab
fn expand_structural_resolve<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    ty: Ty<'tcx>,
) -> Vec<Decl> {
    let (binder, term) = structural_resolve(ctx, ty);
    let param_env = elab.param_env;
    let mut names = elab.namer(CloneLevel::Body, Dependency::StructuralResolve(ty));
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

// TODO Deprecate and fold into LogicElab
fn expand_resolve_func<'tcx>(
    elab: &mut Expander<'_, 'tcx>,
    ctx: &mut Why3Generator<'tcx>,
    def_id: DefId,
    subst: GenericArgsRef<'tcx>,
) -> Vec<Decl> {
    let param_env = elab.param_env;
    let trait_meth_id = ctx.get_diagnostic_item(Symbol::intern("creusot_resolve_method")).unwrap();
    let sig = ctx.sig(def_id).clone();
    let mut pre_sig = EarlyBinder::bind(sig).instantiate(ctx.tcx, subst);
    pre_sig = pre_sig.normalize(ctx.tcx, param_env);

    let arg = Term::var(pre_sig.inputs[0].0, pre_sig.inputs[0].2);
    let body;

    let mut names = elab.namer(CloneLevel::Body, Dependency::Item(def_id, subst));
    let name = names.value(def_id, subst).name;

    let mut sig = named_sig_to_why3(ctx, &mut names, name, &pre_sig, def_id);

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
                sig.retty = None;
                return vec![Decl::predicate(sig, None)];
            }
            traits::TraitResol::NoInstance => {
                // We know there is no instance => body is true
                body = Term::mk_true(ctx.tcx);
            }
        }
    }

    lower_logical_defn(ctx, &mut names, sig, Some(LetKind::Predicate), body)
}

struct TyElab;

impl DepElab for TyElab {
    fn expand<'tcx>(
        elab: &mut Expander<'_, 'tcx>,
        ctx: &mut Why3Generator<'tcx>,
        dep: Dependency<'tcx>,
        level: CloneLevel,
    ) -> Vec<why3::declaration::Decl> {
        assert!(matches!(dep, Dependency::Type(_)));
        // let dep = match dep {
        //     Dependency::Type(_) => todo!(),
        //     Dependency::Builtin(prelude_module) => todo!(),
        //     _ => unreachable!(),
        // };
        let Dependency::Type(ty) = dep else { return Vec::new() };
        let Some((def_id, subst)) = dep.did() else { return Vec::new() };

        let mut names = elab.namer(level, dep);
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
                        Symbol::intern(&format!("{}_Type", module_name(ctx.tcx, def_id)))
                    } else {
                        module_name(ctx.tcx, def_id)
                    };
                    let name = if name.module.is_empty() { name } else { name.module_qname() };
                    let use_decl =
                        Use { as_: Some(name.clone()), name: modl.as_str().into(), export: false };
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
        initial: impl Iterator<Item = (CloneLevel, Dependency<'tcx>)>,
    ) -> Self {
        let mut exp = Self {
            graph: Default::default(),

            namer,
            self_key,
            param_env,
            expansion_queue: initial.map(|(a, b)| (self_key, a, b)).collect(),
            tcx,
            dep_bodies: Default::default(),
            dep_level: Default::default(),
        };
        for dep in &exp.expansion_queue {
            exp.graph.add_edge(dep.0, dep.2, ());
        }

        exp
    }

    fn namer(&mut self, _: CloneLevel, source: Dependency<'tcx>) -> ExpansionProxy<'_, 'tcx> {
        ExpansionProxy {
            namer: &mut self.namer,
            expansion_queue: &mut self.expansion_queue,
            level: CloneLevel::Body,
            source,
        }
    }

    /// Expand the graph with new entries
    pub fn update_graph(
        mut self,
        ctx: &mut Why3Generator<'tcx>,
        _: GraphDepth,
    ) -> (DiGraphMap<Dependency<'tcx>, ()>, HashMap<Dependency<'tcx>, Vec<Decl>>) {
        let mut visited = HashSet::new();
        while let Some((s, l, t)) = self.expansion_queue.pop_front() {
            let t = t.resolve(ctx, self.param_env).unwrap_or(t);
            if !visited.insert((s, l, t)) {
                continue;
            }
            self.graph.add_edge(s, t, ());
            self.expand(ctx, l, t);
        }
        (self.graph, self.dep_bodies)
    }

    fn expand(&mut self, ctx: &mut Why3Generator<'tcx>, level: CloneLevel, dep: Dependency<'tcx>) {
        if self.dep_level.get(&dep).map(|lvl| *lvl >= level).unwrap_or(false) {
            return;
        }
        let decls = match dep {
            Dependency::Type(_) => TyElab::expand(self, ctx, dep, level),
            Dependency::Item(mut def_id, _) => {
                if ctx.is_logical(def_id) {
                    LogicElab::expand(self, ctx, dep, level)
                } else if ctx.is_constant(def_id) {
                    LogicElab::expand(self, ctx, dep, CloneLevel::Body)
                } else if matches!(ctx.def_kind(def_id), DefKind::Field) {
                    if util::item_type(self.tcx, def_id) == ItemType::Field {
                        def_id = self.tcx.parent(def_id);
                    };
                    let name = self.namer.insert(dep).qname();
                    let modl = module_name(ctx.tcx, def_id);
                    let name = if name.module.is_empty() { name } else { name.module_qname() };
                    let use_decl =
                        Use { as_: Some(name.clone()), name: modl.as_str().into(), export: false };
                    vec![Decl::UseDecl(use_decl)]
                } else {
                    ProgElab::expand(self, ctx, dep, level)
                }
            }
            Dependency::TyInvAxiom(_) => LogicElab::expand(self, ctx, dep, level),
            Dependency::StructuralResolve(_) => LogicElab::expand(self, ctx, dep, level),
            Dependency::ClosureSpec(_, _, _) => LogicElab::expand(self, ctx, dep, level),
            Dependency::Builtin(b) => {
                vec![Decl::UseDecl(Use { name: b.qname(), as_: None, export: false })]
            }
        };
        // eprintln!("{:?} {:?} {:?}", self.namer.insert(dep), dep, decls);
        self.dep_bodies.insert(dep, decls);
        self.dep_level.insert(dep, level);
    }
}
