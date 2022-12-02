use std::collections::{HashMap, HashSet};

use creusot_rustc::{
    hir::def_id::DefId,
    macros::{TyDecodable, TyEncodable, TypeFoldable, TypeVisitable},
    middle::ty::{subst::SubstsRef, EarlyBinder, TypeVisitable},
    resolve::Namespace,
    span::{Symbol, DUMMY_SP},
};
use heck::ToUpperCamelCase;
use indexmap::IndexMap;
use petgraph::{
    graphmap::DiGraphMap,
    visit::{DfsPostOrder, Walker},
    EdgeDirection::Outgoing,
};
use rustc_middle::{
    middle::dependency_format::Dependencies,
    ty::{
        subst::{GenericArgKind, InternalSubsts},
        DefIdTree, FloatTy, Ty, TyCtxt, TyKind, TypeVisitor, UintTy,
    },
};
use rustc_type_ir::IntTy;
use util::ItemType;
use why3::{
    declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use},
    QName,
};

use crate::{
    ctx::TranslationCtx,
    pearlite::super_visit_term,
    translation::{
        fmir::{Block, Body, Branches, Expr, RValue, Statement, Terminator},
        interface,
        pearlite::{Term, TermKind, TermVisitor},
        traits::{resolve_opt, TraitImpl},
    },
    util::{self, item_name, item_qname, item_type, module_name, pre_sig_of, PreSignature},
};

use super::Cloner;

// The clone wars are over
// Implements a simpler version of CloneMap, split as two operations: gathering all the 'monomorphic' instances of functions / types used
// and a second why3 specific pass turning that into clones (and later not into clones!)

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug, PartialOrd, Ord, TypeFoldable, TypeVisitable)]
pub enum Dependency<'tcx> {
    // A normal, good Rust function or type
    Item(DefId, SubstsRef<'tcx>),
    // Cannot be a tuple, adt or other composite type.
    // Can be, &mut, &, *mut, [T], [T; N], u32, i32, bool, etc..
    BaseTy(Ty<'tcx>),
}

impl<'tcx> Dependency<'tcx> {
    fn identity(tcx: TyCtxt<'tcx>, id: DefId) -> Self {
        Dependency::Item(id, InternalSubsts::identity_for_item(tcx, id))
    }
}

// Depending on where we are cloning from we will only want to keep
// all or some of our dependencies
#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug, PartialOrd, Ord, TypeFoldable, TypeVisitable)]
pub enum DepLevel {
    Body,
    Signature,
}

// Temporary to start testing
// Eventually dependency tracking should probably move into main part of crate?
fn get_immediate_deps<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    match item_type(ctx.tcx, def_id) {
        ItemType::Type => {
            let substs = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            let tys = ctx
                .adt_def(def_id)
                .all_fields()
                .map(|f| f.ty(ctx.tcx, substs))
                .flat_map(|fld| fld.walk());

            let mut v = Vec::new();

            for arg in tys {
                match arg.unpack() {
                    GenericArgKind::Type(ty) => match ty.kind() {
                        TyKind::Adt(def, sub) => {
                            v.push((DepLevel::Body, Dependency::Item(def.did(), *sub)))
                        }
                        _ => {}
                    },
                    GenericArgKind::Lifetime(_) => {}
                    a => panic!("{a:?}"),
                }
            }
            v
        }
        ItemType::Logic | ItemType::Predicate
            // if def_id.is_local()
            //     && !util::is_trusted(ctx.tcx, def_id)
            //     && util::has_body(ctx, def_id)
                =>
        {
            term_dependencies(ctx, def_id)
        }
        ItemType::Program => program_dependencies(ctx, def_id),
        // Fill out
        ItemType::AssocTy => {let mut deps = Vec::new();
            if ctx.impl_of_method(def_id).is_some() {
                ctx.type_of(def_id).deps(&mut |d| deps.push((DepLevel::Signature, d)));

            }

            deps
        },
        ItemType::Constant => Vec::new(),
        ItemType::Impl => {
            let mut deps = Vec::new();
            ctx.trait_impl(def_id).deps(&mut |d| deps.push((DepLevel::Body, d)));
            deps
        }
        ItemType::Trait => Vec::new(),
        e => todo!("{e:?}"),
    }
}

struct TermDep<F> {
    f: F,
}

// Dumb wrapper trait for syntax
trait VisitDeps<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F);
}

impl<'tcx> VisitDeps<'tcx> for TraitImpl<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        self.refinements.iter().for_each(|r| {
            (f)(Dependency::Item(r.trait_.0, r.trait_.1));
            r.refn.deps(f);
        })
    }
}

impl<'tcx> VisitDeps<'tcx> for Term<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        TermDep { f }.visit_term(self)
    }
}

impl<'tcx> VisitDeps<'tcx> for Ty<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        TermDep { f }.visit_ty(*self);
    }
}

impl<'tcx> VisitDeps<'tcx> for PreSignature<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        self.contract.terms().for_each(|t| {
            t.deps(f);
        });

        self.visit_with(&mut TermDep { f });
    }
}

impl<'tcx> VisitDeps<'tcx> for Expr<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        match self {
            Expr::Place(_) => {}
            Expr::Move(_) => {}
            Expr::Copy(_) => {}
            Expr::BinOp(_, _, l, r) => {
                l.deps(f);
                r.deps(f)
            }
            Expr::UnaryOp(_, e) => e.deps(f),
            Expr::Constructor(id, sub, args) => {
                (f)(Dependency::Item(*id, sub));
                args.iter().for_each(|a| a.deps(f))
            }
            Expr::Call(id, sub, args) => {
                (f)(Dependency::Item(*id, sub));
                args.iter().for_each(|a| a.deps(f))
            }
            Expr::Constant(_) => {}
            Expr::Cast(e, _, _) => e.deps(f),
            Expr::Tuple(args) => args.iter().for_each(|a| a.deps(f)),
            Expr::Span(_, e) => e.deps(f),
            Expr::Len(e) => e.deps(f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for RValue<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        match self {
            RValue::Ghost(t) => t.deps(f),
            RValue::Borrow(_) => {}
            RValue::Expr(e) => e.deps(f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Statement<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        match self {
            Statement::Assignment(_, r) => r.deps(f),
            Statement::Resolve(id, sub, _) => (f)(Dependency::Item(*id, sub)),
            Statement::Assertion(t) => t.deps(f),
            Statement::Invariant(_, t) => t.deps(f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Terminator<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        match self {
            Terminator::Switch(e, b) => {
                e.deps(f);
                b.deps(f)
            }
            _ => {}
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Branches<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        match self {
            Branches::Constructor(adt, sub, _, _) => (f)(Dependency::Item(adt.did(), sub)),
            _ => {}
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Block<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        self.stmts.iter().for_each(|s| s.deps(f));

        self.terminator.deps(f)
    }
}

impl<'tcx> VisitDeps<'tcx> for Body<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, f: &mut F) {
        self.locals.iter().for_each(|(_, _, t)| t.deps(f));

        self.blocks.values().for_each(|b| b.deps(f));
    }
}

impl<'tcx, F: FnMut(Dependency<'tcx>)> TermVisitor<'tcx> for TermDep<F> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        match &term.kind {
            TermKind::Item(id, subst) => (self.f)(Dependency::Item(*id, subst)),
            TermKind::Call { id, subst, fun: _, args: _ } => (self.f)(Dependency::Item(*id, subst)),
            TermKind::Constructor { adt: _, variant: _, fields: _ } => {
                if let TyKind::Adt(def, subst) = term.ty.kind() {
                    (self.f)(Dependency::Item(def.did(), subst))
                } else {
                    unreachable!()
                }
            }
            _ => {}
        };
        super_visit_term(term, self)
    }
}

impl<'tcx, F: FnMut(Dependency<'tcx>)> TypeVisitor<'tcx> for TermDep<F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Adt(def, sub) => (self.f)(Dependency::Item(def.did(), *sub)),
            TyKind::Projection(pty) => (self.f)(Dependency::Item(pty.item_def_id, pty.substs)),
            TyKind::Int(_) | TyKind::Uint(_) => (self.f)(Dependency::BaseTy(t)),
            _ => {}
        };
        std::ops::ControlFlow::Continue(())
    }
}

fn term_dependencies<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    let mut deps = Vec::new();

    let sig = pre_sig_of(ctx, def_id);
    sig.deps(&mut |dep| deps.push((DepLevel::Signature, dep)));

    if let Some(term) = ctx.term(def_id) {
        term.deps(&mut |dep| deps.push((DepLevel::Body, dep)));
    }
    deps
}

fn program_dependencies<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    let mut deps = Vec::new();

    let sig = pre_sig_of(ctx, def_id);
    sig.deps(&mut |dep| deps.push((DepLevel::Signature, dep)));

    if let Some(body) = ctx.fmir_body(def_id) {
        body.deps(&mut |dep| deps.push((DepLevel::Body, dep)));
    }
    deps
}
type MonoGraphInner<'tcx> =
    DiGraphMap<Dependency<'tcx>, (DepLevel, Option<(DefId, SubstsRef<'tcx>)>)>;

#[derive(Default)]
pub struct MonoGraph<'tcx> {
    graph: MonoGraphInner<'tcx>,
    level: IndexMap<Dependency<'tcx>, DepLevel>,
    roots: IndexMap<DefId, Dependency<'tcx>>,
    // roots?
}

impl<'tcx> MonoGraph<'tcx> {
    pub fn new() -> Self {
        MonoGraph { ..Default::default() }
    }

    // FIXME: Make `finished` a part of the graph state. Currently, we will do a bunch of work retraversing the graph over and over again.
    pub fn add_root(&mut self, ctx: &mut TranslationCtx<'tcx>, def_id: DefId) {
        let root = Dependency::identity(ctx.tcx, def_id);
        if self.roots.insert(def_id, root).is_some() {
            return;
        }

        let mut to_visit = vec![root];
        let mut finished = HashSet::new();
        let param_env = ctx.param_env(def_id);
        // eprintln!("adding root {def_id:?}");
        while let Some(next) = to_visit.pop() {
            // eprintln!("visiting {:?}", next);

            if !finished.insert(next) {
                continue;
            }

            self.graph.add_node(next);
            let Dependency::Item(id, subst) = next else { continue };
            self.add_root(ctx, id);
            ctx.translate(id);

            let to_add = get_immediate_deps(ctx, id);
            // eprintln!("deps_of({id:?}) :- {to_add:?}\n");

            for (lvl, dep) in to_add {
                let Dependency::Item(id, orig_subst) = dep else {
                    self.graph.add_edge(next, EarlyBinder(dep).subst(ctx.tcx, subst), (lvl, None));
                    continue
                };

                let subst = EarlyBinder(orig_subst).subst(ctx.tcx, subst);

                let tgt = if let Some(tgt) = closure_hack(ctx.tcx, def_id, subst) {
                    tgt
                } else if can_resolve(ctx, (id, subst)) {
                    resolve_opt(ctx.tcx, param_env, id, subst)
                        .unwrap_or_else(|| panic!("could not resolve {id:?} {subst:?}"))
                } else {
                    ctx.normalize_erasing_regions(param_env, (id, subst))
                };

                // eprintln!("{:?} -> {:?} weight {:?}", next, tgt, (lvl, Some((id, orig_subst))));

                self.graph.add_edge(
                    next,
                    Dependency::Item(tgt.0, tgt.1),
                    (lvl, Some((id, orig_subst))),
                );

                to_visit.push(Dependency::Item(tgt.0, tgt.1));
            }
        }

        // Color the nodes
        for (_, tgt, (lvl, _)) in self.graph.all_edges() {
            debug!("{tgt:?} to {lvl:?}");
            self.level.entry(tgt).and_modify(|a| *a = (*a).max(*lvl)).or_insert(*lvl);
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = Dependency<'tcx>> + '_ {
        MonoGraphIter {
            walker: DfsPostOrder::empty(&self.graph),
            roots: self.roots.values().cloned(),
        }
        .iter(&self.graph)
    }
}

struct MonoGraphIter<'tcx, I> {
    walker: DfsPostOrder<Dependency<'tcx>, HashSet<Dependency<'tcx>>>,
    roots: I,
}

impl<'tcx, I: Iterator<Item = Dependency<'tcx>>> Walker<&MonoGraphInner<'tcx>>
    for MonoGraphIter<'tcx, I>
{
    type Item = Dependency<'tcx>;

    fn walk_next(&mut self, context: &MonoGraphInner<'tcx>) -> Option<Self::Item> {
        match self.walker.walk_next(context) {
            Some(x) => Some(x),
            None => {
                let next_root = self.roots.next()?;
                self.walker.move_to(next_root);
                self.walker.walk_next(context)
            }
        }
    }
}

fn closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Option<(DefId, SubstsRef<'tcx>)> {
    if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("fn_impl_resolve"), def_id)
    {
        debug!("closure_hack: {:?}", def_id);
        let self_ty = subst.types().nth(1).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return Some((*id, csubst));
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return Some((*id, csubst));
        }
    }

    None
}

fn can_resolve<'tcx>(ctx: &mut TranslationCtx<'tcx>, dep: (DefId, SubstsRef<'tcx>)) -> bool {
    ctx.trait_of_item(dep.0).is_some()
}

#[derive(Debug)]
pub struct Names<'tcx> {
    names: IndexMap<(DefId, SubstsRef<'tcx>), why3::Ident>,
}

impl<'tcx> Names<'tcx> {
    pub(super) fn get(&self, tgt: (DefId, SubstsRef<'tcx>)) -> why3::Ident {
        self.names.get(&tgt).unwrap_or_else(|| panic!("Could not find {:?}", tgt)).clone()
    }

    // // FIXME
    // pub(crate) fn ty(&self, id: DefId, sub: SubstsRef<'tcx>) -> QName {
    //     self.get((id, sub))
    // }

    // //FIXME
    // pub(crate) fn value(&self, id: DefId, sub: SubstsRef<'tcx>) -> QName {
    //     self.get((id, sub))
    // }
}

pub(crate) fn name_clones<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    graph: &MonoGraph<'tcx>,
    root: Dependency<'tcx>,
) -> Names<'tcx> {
    let mut names = IndexMap::new();
    let mut assigned = IndexMap::new();
    let walk = DfsPostOrder::new(&graph.graph, root);

    for node in walk.iter(&graph.graph) {
        let Dependency::Item(def_id, subst) = node else { continue };

        let count = assigned.entry(def_id).or_insert(0);

        let base_sym = match util::item_type(ctx.tcx, def_id) {
            ItemType::Impl => ctx.tcx.item_name(ctx.tcx.trait_id_of_impl(def_id).unwrap()),
            ItemType::Closure => Symbol::intern(&format!(
                "closure{}",
                ctx.tcx.def_path(def_id).data.last().unwrap().disambiguator
            )),
            _ => ctx.tcx.item_name(def_id),
        };

        names.insert(
            (def_id, subst),
            format!("{}{}", base_sym.as_str().to_upper_camel_case(), count).into(),
        );
    }

    // for node in graph.graph.nodes() {
    //     let Dependency::Item(def_id, subst) = node else { continue };

    //     let count = assigned.entry(def_id).or_insert(0);

    //     let base_sym = match util::item_type(ctx.tcx, def_id) {
    //         ItemType::Impl => ctx.tcx.item_name(ctx.tcx.trait_id_of_impl(def_id).unwrap()),
    //         ItemType::Closure => Symbol::intern(&format!(
    //             "closure{}",
    //             ctx.tcx.def_path(def_id).data.last().unwrap().disambiguator
    //         )),
    //         _ => ctx.tcx.item_name(def_id),
    //     };
    //     names.insert(
    //         (def_id, subst),
    //         QName {
    //             module: vec![format!("{}{}", base_sym.as_str().to_upper_camel_case(), count).into()],
    //             name: item_name(ctx.tcx, def_id, Namespace::ValueNS),
    //         },
    //     );
    // }
    Names { names }
}

// Temporary, eventually provided via a cached query
// A map of the public clones in each definition
pub struct PriorClones<'a, 'tcx> {
    prior: IndexMap<DefId, Names<'tcx>>,
    graph: &'a MonoGraph<'tcx>,
}

#[derive(Clone, Copy)]
pub struct Namer<'a, 'tcx> {
    priors: &'a PriorClones<'a, 'tcx>,
    id: DefId,
    tcx: TyCtxt<'tcx>,
}

impl<'tcx> Cloner<'tcx> for Namer<'_, 'tcx> {
    fn value(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let base = self.priors.prior.get(&self.id).unwrap().get((def_id, subst));
        QName { module: vec![base], name: item_name(self.tcx, def_id, Namespace::ValueNS) }
    }

    fn ty(&mut self, def_id: DefId, subst: SubstsRef<'tcx>) -> QName {
        let base = self.priors.prior.get(&self.id).unwrap().get((def_id, subst));
        QName { module: vec![base], name: item_name(self.tcx, def_id, Namespace::TypeNS) }
    }

    fn accessor(
        &mut self,
        def_id: DefId,
        subst: SubstsRef<'tcx>,
        variant: usize,
        ix: usize,
    ) -> QName {
        let base = self.priors.prior.get(&self.id).unwrap().get((def_id, subst));
        QName { module: vec![base], name: item_name(self.tcx, def_id, Namespace::ValueNS) }
    }

    fn constructor(&mut self, def_id: DefId, subst: SubstsRef<'tcx>, variant: usize) -> QName {
        let base = self.priors.prior.get(&self.id).unwrap().get((def_id, subst));
        QName { module: vec![base], name: item_name(self.tcx, def_id, Namespace::ValueNS) }
    }

    fn to_clones(&mut self, ctx: &mut TranslationCtx<'tcx>, clone_level: CloneLevel) -> Vec<Decl> {
        make_clones(ctx, *self, clone_level, self.id)
    }
}

impl<'a, 'tcx> PriorClones<'a, 'tcx> {
    //     pub(crate) fn from_deps(ctx: &TranslationCtx<'tcx>) -> Self {
    //         let mut prior = IndexMap::new();

    //         for (id, summ) in &ctx.dependencies {
    //             let mut clones = IndexMap::new();
    //             for (k, info) in summ {
    //                 clones.insert(*k, info.qname(ctx.tcx, k.0));
    //             }
    //             prior.insert(*id, clones);
    //         }

    //         PriorClones { prior }
    //     }

    pub(crate) fn from_graph(ctx: &mut TranslationCtx<'tcx>, graph: &'a MonoGraph<'tcx>) -> Self {
        let mut clones = IndexMap::new();

        for node in graph.roots.values() {
            let Dependency::Item(def_id, _) = node else { continue };

            // eprintln!("naming for {node:?}");
            if !clones.contains_key(def_id) {
                clones.insert(*def_id, name_clones(ctx, graph, *node));
            }
        }

        PriorClones { graph, prior: clones }
    }

    // pub(crate) fn get(&self, inside: DefId) -> Option<&Names<'tcx>> {
    //     self.prior.get(&inside)
    //     // .map(|q| q.clone())
    //     //             .unwrap_or_else(|| QName::from_string("INVALID.prior").unwrap())
    // }

    pub(crate) fn get(&'a self, tcx: TyCtxt<'tcx>, inside: DefId) -> Namer<'a, 'tcx> {
        // eprintln!("cloning {inside:?}");
        Namer { priors: self, id: inside, tcx }
    }
}

// Transform a graph into a set of clones
pub fn make_clones<'tcx, 'a>(
    ctx: &mut TranslationCtx<'tcx>,
    priors: Namer<'a, 'tcx>,
    level: CloneLevel,
    root: DefId,
) -> Vec<Decl> {
    let Namer { priors, id, .. } = priors;
    let mut names = priors.get(ctx.tcx, root);
    let root = Dependency::Item(root, InternalSubsts::identity_for_item(ctx.tcx, root));
    let mut topo = DfsPostOrder::new(&priors.graph.graph, root);

    let desired_dep_level = match level {
        CloneLevel::Stub => DepLevel::Body, // Stub clones need a separate, shallow traversal of the graph
        CloneLevel::Interface => DepLevel::Signature,
        CloneLevel::Body => DepLevel::Body,
    };

    let mut clones = Vec::new();
    let mut uses = Vec::new();

    while let Some(node) = topo.walk_next(&priors.graph.graph) {
        if node == root {
            continue;
        }

        if priors.graph.level[&node] < desired_dep_level {
            continue;
        };

        // eprintln!("cloning {node:?} at level {:?}", priors.graph.level[&node]);

        let (id, subst) = match node {
            Dependency::Item(id, subst) => (id, subst),
            Dependency::BaseTy(ty) => {
                uses.push(Decl::UseDecl(Use { name: base_ty_name(ty), as_: None }));
                continue;
            }
        };

        if item_type(ctx.tcx, id) == ItemType::Type {
            let name = item_qname(ctx, id, Namespace::TypeNS).module_qname();
            uses.push(Decl::UseDecl(Use { name: name.clone(), as_: Some(name) }));
            continue;
        };

        let mut clone_subst = base_subst(ctx, priors, id, subst);

        let mut node_names = priors.get(ctx.tcx, id);
        // eprintln!("{:?}", priors.prior[&id]);
        // eprintln!("{:?}", priors.graph.graph);
        for dep in priors.graph.graph.neighbors_directed(node, Outgoing) {
            let (_, orig) = priors.graph.graph[(node, dep)];
            if priors.graph.level[&dep] < desired_dep_level {
                continue;
            };

            let Dependency::Item(id, subst) = dep else {continue };
            let orig = orig.unwrap();
            // FIXME: Not really correct
            if item_type(ctx.tcx, orig.0) == ItemType::Type {
                continue;
            }

            // eprintln!("{:?} depends on {:?}", node, dep);
            // eprintln!("getting name for {:?} originally called {:?}", (dep), priors.graph.graph[(node, dep)]);
            clone_subst
                .push(CloneSubst::Val(node_names.value(orig.0, orig.1), names.value(id, subst)))
        }

        let clone = DeclClone {
            name: cloneable_name(ctx, id, level),
            subst: clone_subst,
            kind: CloneKind::Named(names.value(id, subst).module_ident().unwrap().clone()),
        };
        clones.push(Decl::Clone(clone));
    }

    uses.into_iter().chain(clones).collect()
}

fn base_ty_name(ty: Ty) -> QName {
    match ty.kind() {
        TyKind::Bool => QName::from_string("prelude.Bool").unwrap(),
        TyKind::Char => QName::from_string("prelude.Char").unwrap(),
        TyKind::Int(IntTy::I8) => QName::from_string("prelude.Int8").unwrap(),
        TyKind::Int(IntTy::I16) => QName::from_string("prelude.Int16").unwrap(),
        TyKind::Int(IntTy::I32) => QName::from_string("mach.int.Int32").unwrap(),
        TyKind::Int(IntTy::I64) => QName::from_string("mach.int.Int64").unwrap(),
        TyKind::Int(IntTy::I128) => QName::from_string("prelude.Int128").unwrap(),
        TyKind::Uint(UintTy::U8) => QName::from_string("prelude.UInt8").unwrap(),
        TyKind::Uint(UintTy::U16) => QName::from_string("prelude.UInt16").unwrap(),
        TyKind::Uint(UintTy::U32) => QName::from_string("mach.int.UInt32").unwrap(),
        TyKind::Uint(UintTy::U64) => QName::from_string("mach.int.UInt64").unwrap(),
        TyKind::Uint(UintTy::U128) => QName::from_string("prelude.UInt128").unwrap(),
        TyKind::Int(IntTy::Isize) => QName::from_string("prelude.IntSize").unwrap(),
        TyKind::Uint(UintTy::Usize) => QName::from_string("prelude.UIntSize").unwrap(),
        TyKind::Float(FloatTy::F32) => QName::from_string("ieee_float.Float32").unwrap(),
        TyKind::Float(FloatTy::F64) => QName::from_string("ieee_float.Float64").unwrap(),
        TyKind::Str => todo!(),
        TyKind::Slice(_) => QName::from_string("prelude.Slice").unwrap(),
        TyKind::RawPtr(_) => todo!(),
        TyKind::Ref(_, _, _) => QName::from_string("prelude.Borrow").unwrap(),
        TyKind::Never => todo!(),
        TyKind::Tuple(_) => todo!(),
        _ => panic!("base_ty_name: can only be called on basic types. {ty:?}"),
    }
}
// PreludeModule::Int => QName::from_string("mach.int.Int").unwrap(),
// PreludeModule::Opaque => QName::from_string("prelude.Opaque").unwrap(),
// PreludeModule::Ref => QName::from_string("Ref").unwrap(),
// PreludeModule::Seq => QName::from_string("seq.Seq").unwrap(),

pub fn base_subst<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    names: &PriorClones<'_, 'tcx>,
    mut def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Vec<CloneSubst> {
    use creusot_rustc::middle::ty::GenericParamDefKind;
    use heck::ToSnakeCase;
    loop {
        if ctx.tcx.is_closure(def_id) {
            def_id = ctx.tcx.parent(def_id);
        } else {
            break;
        }
    }
    let trait_params = ctx.tcx.generics_of(def_id);
    let mut clone_subst = Vec::new();

    if subst.is_empty() {
        return Vec::new();
    }

    for ix in 0..trait_params.count() {
        let p = trait_params.param_at(ix, ctx.tcx);
        let ty = subst[ix];
        if let GenericParamDefKind::Type { .. } = p.kind {
            let ty = crate::backend::ty::translate_ty(
                ctx,
                &mut names.get(ctx.tcx, def_id),
                DUMMY_SP,
                ty.expect_ty(),
            );
            clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
        }
    }

    clone_subst
}

// Which kind of module should we clone
// TODO: Unify with `CloneOpacity`
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum CloneLevel {
    Stub,
    Interface,
    Body,
}

fn cloneable_name(ctx: &TranslationCtx, def_id: DefId, interface: CloneLevel) -> QName {
    use util::ItemType::*;

    // TODO: Refactor.
    match util::item_type(ctx.tcx, def_id) {
        Logic | Predicate | Impl => match interface {
            CloneLevel::Stub => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx, def_id)).into(),
            },
            CloneLevel::Interface => interface::interface_name(ctx, def_id).into(),
            CloneLevel::Body => module_name(ctx, def_id).into(),
        },
        Program | Closure => {
            QName { module: Vec::new(), name: interface::interface_name(ctx, def_id) }
        }
        Constant | Trait | Type | AssocTy => module_name(ctx, def_id).into(),
        Unsupported(_) => unreachable!(),
    }
}
