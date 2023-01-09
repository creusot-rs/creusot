use std::collections::HashSet;

use creusot_rustc::{
    ast::Mutability,
    hir::{def::DefKind, def_id::DefId},
    macros::{TypeFoldable, TypeVisitable},
    middle::ty::{subst::SubstsRef, EarlyBinder, TypeVisitable},
    resolve::Namespace,
    span::{Symbol, DUMMY_SP},
};
use heck::ToUpperCamelCase;
use indexmap::{IndexMap, IndexSet};
use petgraph::{
    data::Build,
    dot::{Config, Dot},
    graphmap::DiGraphMap,
    visit::{DfsPostOrder, EdgeFiltered, Walker},
    EdgeDirection::Outgoing,
};
use rustc_middle::{
    mir::{tcx::PlaceTy, PlaceElem},
    ty::{
        subst::{GenericArgKind, InternalSubsts},
        DefIdTree, FloatTy, List, ProjectionTy, Ty, TyCtxt, TyKind, TypeFoldable,
        TypeSuperVisitable, TypeVisitor, UintTy,
    },
};
use rustc_type_ir::IntTy;
use util::ItemType;
use why3::{
    declaration::{CloneKind, CloneSubst, Decl, DeclClone, Use},
    QName,
};

use crate::{
    backend::ty::translate_ty,
    ctx::TranslationCtx,
    pearlite::super_visit_term,
    translation::{
        fmir::{Block, Body, Branches, Expr, Place, RValue, Statement, Terminator},
        function::closure_contract2,
        pearlite::{Term, TermKind, TermVisitor},
        traits::{resolve_opt, TraitImpl},
    },
    util::{self, get_builtin, item_name, item_qname, item_type, module_name, PreSignature},
};
use creusot_rustc::macros::{TyDecodable, TyEncodable};

use super::Cloner;

// The clone wars are over
// Implements a simpler version of CloneMap, split as two operations: gathering all the 'monomorphic' instances of functions / types used
// and a second why3 specific pass turning that into clones (and later not into clones!)

#[derive(
    Clone,
    Copy,
    Hash,
    PartialEq,
    Eq,
    Debug,
    PartialOrd,
    Ord,
    TyEncodable,
    TyDecodable,
    TypeFoldable,
    TypeVisitable,
)]
pub(crate) enum ClosureId {
    Type,
    Unnest,
    Resolve,
    Precondition,
    PostconditionOnce,
    PostconditionMut,
    Postcondition,
    Field,
}

#[derive(
    Clone,
    Copy,
    Hash,
    PartialEq,
    Eq,
    Debug,
    PartialOrd,
    Ord,
    TyEncodable,
    TyDecodable,
    TypeFoldable,
    TypeVisitable,
)]
pub struct Id(pub(crate) DefId, pub(crate) Option<ClosureId>);

impl ClosureId {
    pub(crate) fn name(&self) -> &str {
        match self {
            ClosureId::Type => "Type",
            ClosureId::Unnest => "Unnest",
            ClosureId::Resolve => "Resolve",
            ClosureId::Precondition => "Precondition",
            ClosureId::PostconditionOnce => "PostconditionOnce",
            ClosureId::PostconditionMut => "PostconditionMut",
            ClosureId::Postcondition => "Postcondition",
            ClosureId::Field => "Field",
        }
    }
}

impl From<DefId> for Id {
    fn from(value: DefId) -> Self {
        Id(value, None)
    }
}

impl From<&DefId> for Id {
    fn from(value: &DefId) -> Self {
        Id(*value, None)
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Debug, PartialOrd, Ord, TypeFoldable, TypeVisitable)]
pub(crate) enum Dependency<'tcx> {
    // A normal, good Rust function or type
    Item(Id, SubstsRef<'tcx>),
    // Cannot be a tuple, adt or other composite type.
    // Can be, &mut, &, *mut, [T], [T; N], u32, i32, bool, etc..
    // TODO: Probably should relax this restriction and allow aggregate types and typarams in here
    BaseTy(Ty<'tcx>),
}

impl<'tcx> Dependency<'tcx> {
    pub(crate) fn identity(tcx: TyCtxt<'tcx>, id: Id) -> Self {
        Dependency::Item(id, tcx.erase_regions(identity_substs_for(tcx, id.0)))
    }

    fn as_ty(self, tcx: TyCtxt<'tcx>) -> Ty<'tcx> {
        match self {
            Self::BaseTy(ty) => ty,
            Self::Item(id, substs) => match util::item_type(tcx, id.0) {
                ItemType::AssocTy => tcx.mk_projection(id.0, substs),
                ItemType::Type => tcx.mk_adt(tcx.adt_def(id.0), substs),
                _ => unreachable!(),
            },
        }
    }

    fn as_item(&self) -> Option<(Id, SubstsRef<'tcx>)> {
        match self {
            Dependency::Item(id, s) => Some((*id, s)),
            Dependency::BaseTy(_) => None,
        }
    }

    fn from_ty(ty: Ty<'tcx>) -> Option<Self> {
        match ty.kind() {
            TyKind::Adt(adt, subst) => Some(Self::Item(adt.did().into(), subst)),
            TyKind::Closure(id, subst) => Some(Self::Item(Id(*id, Some(ClosureId::Type)), subst)),
            TyKind::Projection(ProjectionTy { substs, item_def_id }) => {
                Some(Self::Item(item_def_id.into(), substs))
            }
            TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Ref(_, _, _)
            | TyKind::Bool
            | TyKind::Array(_, _)
            | TyKind::Slice(_) => Some(Self::BaseTy(ty)),
            // Should this be tuple?
            TyKind::Tuple(_) | TyKind::Param(_) => Some(Self::BaseTy(ty)),
            TyKind::FnPtr(_) | TyKind::FnDef(_, _) => None,
            _ => unreachable!("{ty:?}"),
            // _ => Some(Self::BaseTy(ty)),
        }
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
    id: Id,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    let tcx = ctx.tcx;
    let def_id = id.0;
    match item_type(ctx.tcx, def_id) {
        ItemType::Type => {
            if util::is_trusted(tcx, def_id) {
                return Vec::new();
            }

            let substs = InternalSubsts::identity_for_item(ctx.tcx, def_id);
            let tys = ctx
                .adt_def(def_id)
                .all_fields()
                .map(|f| f.ty(ctx.tcx, substs))
                .flat_map(|fld| fld.walk());

            let mut v = Vec::new();

            for arg in tys {
                match arg.unpack() {
                    GenericArgKind::Type(ty) => {
                        ty.deps(tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                    }
                    GenericArgKind::Lifetime(_) => {}
                    // TODO: slightly wrong if there are const args
                    GenericArgKind::Const(_) => {} // a => panic!("{a:?}"),
                }
            }
            v
        }
        ItemType::Logic | ItemType::Predicate => term_dependencies(ctx, def_id),
        ItemType::Closure => match id.1 {
            Some(ClosureId::Type) => {
                let TyKind::Closure(_, subst) = ctx.type_of(id.0).kind() else { unreachable!() };

                let mut v = Vec::new();

                subst
                    .as_closure()
                    .upvar_tys()
                    .for_each(|ty| ty.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep))));
                v
            }
            Some(ClosureId::Resolve) => {
                let mut v = Vec::new();

                let contracts = closure_contract2(ctx, id.0);
                contracts.resolve.0.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Signature, dep)));
                contracts.resolve.1.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                v
            }
            Some(ClosureId::Precondition) => {
                let mut v = Vec::new();

                let contracts = closure_contract2(ctx, id.0);
                contracts.precond.0.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Signature, dep)));
                contracts.precond.1.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                v
            }
            Some(ClosureId::PostconditionOnce) => {
                let mut v = Vec::new();

                let contracts = closure_contract2(ctx, id.0);
                contracts.postcond_once.map(|post| {
                    post.0.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Signature, dep)));
                    post.1.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                });
                v
            }
            Some(ClosureId::PostconditionMut) => {
                let mut v = Vec::new();

                let contracts = closure_contract2(ctx, id.0);
                contracts.postcond_mut.map(|post| {
                    post.0.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Signature, dep)));
                    post.1.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                });
                v
            }
            Some(ClosureId::Postcondition) => {
                let mut v = Vec::new();

                let contracts = closure_contract2(ctx, id.0);
                contracts.postcond.map(|post| {
                    post.0.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Signature, dep)));
                    post.1.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                });
                v
            }
            Some(ClosureId::Unnest) => {
                let mut v = Vec::new();

                let contracts = closure_contract2(ctx, id.0);
                contracts.unnest.map(|unnest| {
                    unnest.0.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Signature, dep)));
                    unnest.1.deps(ctx.tcx, &mut |dep| v.push((DepLevel::Body, dep)));
                });
                v
            }
            Some(ClosureId::Field) => {
                todo!()
            }
            None => program_dependencies(ctx, def_id),
        },
        ItemType::Program => program_dependencies(ctx, def_id),
        // Fill out
        ItemType::AssocTy => {
            let mut deps = Vec::new();
            if ctx.impl_of_method(def_id).is_some() {
                ctx.type_of(def_id).deps(tcx, &mut |d| deps.push((DepLevel::Signature, d)));
            }

            deps
        }
        ItemType::Constant => {
            let mut deps = Vec::new();
            ctx.type_of(def_id).deps(tcx, &mut |d| deps.push((DepLevel::Signature, d)));
            deps
        }
        ItemType::Impl => {
            let mut deps = Vec::new();
            ctx.trait_impl(def_id).deps(tcx, &mut |d| deps.push((DepLevel::Body, d)));
            deps
        }
        ItemType::Trait => Vec::new(),
        ItemType::Field => {
            let parent = ctx.parent(def_id);
            let type_id = match ctx.def_kind(parent) {
                DefKind::Variant => ctx.parent(parent),
                DefKind::Struct | DefKind::Enum | DefKind::Union | DefKind::Closure => parent,
                _ => unreachable!(),
            };

            let mut v =
                vec![(DepLevel::Signature, Dependency::from_ty(ctx.type_of(type_id)).unwrap())];
            if let Some(dep) = Dependency::from_ty(ctx.type_of(def_id)) {
                v.push((DepLevel::Signature, dep));
            }

            v
        }
        e => todo!("{e:?}"),
    }
}

struct TermDep<'tcx, F> {
    f: F,
    tcx: TyCtxt<'tcx>,
}

// Dumb wrapper trait for syntax
trait VisitDeps<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F);
}

impl<'tcx> VisitDeps<'tcx> for TraitImpl<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.refinements.iter().for_each(|r| {
            (f)(Dependency::Item(r.trait_.0.into(), r.trait_.1));
            r.refn.deps(tcx, f);
        })
    }
}

impl<'tcx> VisitDeps<'tcx> for Term<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        TermDep { f, tcx }.visit_term(self)
    }
}

impl<'tcx> VisitDeps<'tcx> for Ty<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        TermDep { f, tcx }.visit_ty(*self);
    }
}

impl<'tcx> VisitDeps<'tcx> for PreSignature<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.contract.terms().for_each(|t| {
            t.deps(tcx, f);
        });

        self.visit_with(&mut TermDep { f, tcx });
    }
}

impl<'tcx> VisitDeps<'tcx> for Expr<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Expr::Place(p) => p.deps(tcx, f),
            Expr::Move(p) => p.deps(tcx, f),
            Expr::Copy(p) => p.deps(tcx, f),
            Expr::BinOp(_, _, l, r) => {
                l.deps(tcx, f);
                r.deps(tcx, f)
            }
            Expr::UnaryOp(_, e) => e.deps(tcx, f),
            Expr::Constructor(id, _, sub, args) => {
                // NOTE: we actually insert a dependency on the type and not hte constructor itself
                // in the interest of coherence we may want ot change that.. idk

                let id = match tcx.def_kind(id) {
                    DefKind::Variant => tcx.parent(*id),
                    _ => *id,
                };
                (f)(Dependency::Item(id.into(), sub));
                args.iter().for_each(|a| a.deps(tcx, f))
            }
            Expr::Call(id, sub, args) => {
                (f)(Dependency::Item(id.into(), sub));
                args.iter().for_each(|a| a.deps(tcx, f))
            }
            Expr::Constant(e) => e.deps(tcx, f),
            Expr::Cast(e, _, _) => e.deps(tcx, f),
            Expr::Tuple(args) => args.iter().for_each(|a| a.deps(tcx, f)),
            Expr::Span(_, e) => e.deps(tcx, f),
            Expr::Len(e) => e.deps(tcx, f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for RValue<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            RValue::Ghost(t) => t.deps(tcx, f),
            RValue::Borrow(p) => p.deps(tcx, f),
            RValue::Expr(e) => e.deps(tcx, f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Statement<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Statement::Assignment(p, r) => {
                p.deps(tcx, f);
                r.deps(tcx, f)
            }
            Statement::Resolve(id, sub, pl) => {
                (f)(Dependency::Item(*id, sub));

                pl.deps(tcx, f)
            }
            Statement::Assertion(t) => t.deps(tcx, f),
            Statement::Invariant(_, t) => t.deps(tcx, f),
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Terminator<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Terminator::Switch(e, b) => {
                e.deps(tcx, f);
                b.deps(tcx, f)
            }
            _ => {}
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Branches<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, _: TyCtxt<'tcx>, f: &mut F) {
        match self {
            Branches::Constructor(adt, sub, _, _) => (f)(Dependency::Item(adt.did().into(), sub)),
            _ => {}
        }
    }
}

impl<'tcx> VisitDeps<'tcx> for Block<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.stmts.iter().for_each(|s| s.deps(tcx, f));

        self.terminator.deps(tcx, f)
    }
}

impl<'tcx> VisitDeps<'tcx> for Body<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        self.locals.iter().for_each(|(_, _, t)| t.deps(tcx, f));

        self.blocks.values().for_each(|b| b.deps(tcx, f));
    }
}

impl<'tcx> VisitDeps<'tcx> for Place<'tcx> {
    fn deps<F: FnMut(Dependency<'tcx>)>(&self, tcx: TyCtxt<'tcx>, f: &mut F) {
        let mut ty = PlaceTy::from_ty(self.ty);
        for elem in self.projection {
            match elem {
                PlaceElem::Field(ix, _) => {
                    match ty.ty.kind() {
                        TyKind::Adt(def, subst) => {
                            let variant_id = ty.variant_index.unwrap_or_else(|| 0u32.into());
                            let variant = &def.variants()[variant_id];
                            let field = &variant.fields[ix.as_usize()];

                            (f)(Dependency::Item(field.did.into(), subst))
                            // eprintln!("{:?}", field);
                        }
                        _ => {}
                    }
                    // eprintln!("base_ty: {ty:?} field_ty: {fty:?}")
                }
                _ => {}
            };
            ty = ty.projection_ty(tcx, elem);
        }
    }
}

impl<'tcx, F: FnMut(Dependency<'tcx>)> TermVisitor<'tcx> for TermDep<'tcx, F> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        match &term.kind {
            TermKind::Binary { .. } => (self.f)(Dependency::Item(
                self.tcx.get_diagnostic_item(Symbol::intern("creusot_int")).unwrap().into(),
                List::empty(),
            )),
            TermKind::Item(id, subst) => (self.f)(Dependency::Item(*id, subst)),
            TermKind::Call { id, subst, fun: _, args: _ } => {
                subst.visit_with(self);
                (self.f)(Dependency::Item(*id, subst))
            }
            TermKind::Constructor { adt: _, variant: _, fields: _ } => {
                if let TyKind::Adt(def, subst) = term.ty.kind() {
                    (self.f)(Dependency::Item(def.did().into(), subst))
                } else {
                    unreachable!()
                }
            }
            TermKind::Projection { name, def, substs, .. } => {
                if self.tcx.is_closure(def.0) {
                    (self.f)(Dependency::Item(*def, substs))
                } else {
                    let adt = self.tcx.adt_def(def.0);
                    let field = &adt.variants()[0u32.into()].fields[name.as_usize()];
                    (self.f)(Dependency::Item(field.did.into(), substs))
                }
            }
            TermKind::Lit(_) => {
                self.visit_ty(term.ty);
            }
            _ => {}
        };
        super_visit_term(term, self)
    }
}

impl<'tcx, F: FnMut(Dependency<'tcx>)> TypeVisitor<'tcx> for TermDep<'tcx, F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Adt(def, sub) => {
                sub.visit_with(self);
                (self.f)(Dependency::Item(def.did().into(), *sub))
            }
            TyKind::Closure(def, sub) => {
                (self.f)(Dependency::Item(Id(*def, Some(ClosureId::Type)), sub));
            }
            TyKind::Projection(pty) => {
                (self.f)(Dependency::Item(pty.item_def_id.into(), pty.substs))
            }
            TyKind::Int(_) | TyKind::Uint(_) => (self.f)(Dependency::BaseTy(t)),
            TyKind::Ref(_, _, Mutability::Mut) => (self.f)(Dependency::BaseTy(t)),
            TyKind::RawPtr(_) => (self.f)(Dependency::BaseTy(t)),
            TyKind::Bool => (self.f)(Dependency::BaseTy(t)),
            TyKind::Char => (self.f)(Dependency::BaseTy(t)),
            _ => {}
        };
        t.super_visit_with(self)
    }
}

fn term_dependencies<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    let mut deps = IndexSet::new();
    let tcx = ctx.tcx;
    let sig = ctx.sig(def_id);
    sig.deps(tcx, &mut |dep| {
        deps.insert((DepLevel::Signature, dep));
    });

    let tcx = ctx.tcx;
    if let Some(term) = ctx.term(def_id) {
        term.deps(tcx, &mut |dep| {
            deps.insert((DepLevel::Body, dep));
        });
    }
    deps.into_iter().collect()
}

fn program_dependencies<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    def_id: DefId,
) -> Vec<(DepLevel, Dependency<'tcx>)> {
    let mut deps = IndexSet::new();
    let tcx = ctx.tcx;
    let sig = ctx.sig(def_id);
    sig.deps(tcx, &mut |dep| {
        deps.insert((DepLevel::Signature, dep));
    });

    let tcx = ctx.tcx;
    if let Some(body) = ctx.fmir_body(def_id) {
        body.deps(tcx, &mut |dep| {
            deps.insert((DepLevel::Body, dep));
        });
    }
    deps.into_iter().collect()
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum EdgeType<'tcx> {
    Refinement(Id, SubstsRef<'tcx>),
    Fake,
    Type,
}
// Move `DepLevel` into `EdgeType::Refinement`?

type MonoGraphInner<'tcx> = DiGraphMap<Dependency<'tcx>, (DepLevel, EdgeType<'tcx>)>;

#[derive(Default)]
pub struct MonoGraph<'tcx> {
    pub(crate) graph: MonoGraphInner<'tcx>,
    level: IndexMap<Dependency<'tcx>, DepLevel>,
    pub(crate) roots: IndexMap<Id, Dependency<'tcx>>,
    // roots?
}

struct PrintParam;

impl<'tcx> TypeVisitor<'tcx> for PrintParam {
    type BreakTy = !;

    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Ref(_, _, _) => eprintln!("{:?}", t.kind()),
            TyKind::Param(p) => eprintln!("visit {p:?}"),
            _ => {}
        }
        t.super_visit_with(self)
    }
}
impl<'tcx> MonoGraph<'tcx> {
    pub(crate) fn new() -> Self {
        MonoGraph { ..Default::default() }
    }

    // FIXME: Make `finished` a part of the graph state. Currently, we will do a bunch of work retraversing the graph over and over again.
    pub(crate) fn add_root(&mut self, ctx: &mut TranslationCtx<'tcx>, def_id: Id) {
        // FIXME: WRONG
        let root = Dependency::identity(ctx.tcx, def_id);
        if self.roots.insert(def_id, root).is_some() {
            return;
        }

        let mut to_visit = vec![root];
        let mut finished = HashSet::new();
        let param_env = ctx.erase_regions(ctx.param_env(def_id.0));

        while let Some(next) = to_visit.pop() {
            // eprintln!("visiting {:?}", next);

            if !finished.insert(next) {
                continue;
            }

            let Dependency::Item(id, subst) = next else { continue };
            self.add_root(ctx, id);

            walk_projections(subst, |ty| {
                self.add_edge(
                    ctx.tcx,
                    next,
                    Dependency::from_ty(ty).unwrap(),
                    (DepLevel::Body, EdgeType::Type),
                );
            });
            subst.types().filter_map(Dependency::from_ty).for_each(|dep| {
                // eprintln!("subst_edge: {next:?} {dep:?}");
                self.add_edge(ctx.tcx, next, dep, (DepLevel::Signature, EdgeType::Type));
            });

            let to_add = get_immediate_deps(ctx, id);

            // to_add.extend(subst.types().filter_map(|ty| Some((DepLevel::Signature, Dependency::from_ty(ty)?)) ));
            // if ctx.def_path_str(id.0).contains("produces") {
            // eprintln!("deps_of({id:?}, {subst:?}) :- {to_add:?}\n");
            // }

            for (lvl, dep) in to_add {
                let Dependency::Item(id, orig_subst) = dep else {
                    self.add_edge(ctx.tcx, next, EarlyBinder(dep).subst(ctx.tcx, subst), (lvl, EdgeType::Type));
                    continue
                };

                let subst = EarlyBinder(orig_subst).subst(ctx.tcx, subst);

                // TODO: clean up
                let tgt = if let Some(tgt) = is_closure_hack(ctx.tcx, id, subst) {
                    Some(Dependency::Item(tgt.0, tgt.1))
                } else if util::item_type(ctx.tcx, id.0) == ItemType::AssocTy {
                    let proj_ty = ProjectionTy { item_def_id: id.0, substs: subst };
                    let ty = ctx.mk_ty(TyKind::Projection(proj_ty));

                    let normed = ctx.try_normalize_erasing_regions(param_env, ty);
                    let _res = resolve_opt(ctx.tcx, param_env, id.0, subst);

                    if let Ok(normed) = normed && ty != normed {
                        match normed.kind() {
                            TyKind::Projection(pty) => Some(Dependency::Item(pty.item_def_id.into(), pty.substs)),
                            _ => Dependency::from_ty(normed),
                        }
                    } else {
                        Dependency::from_ty(ty)
                    }
                } else if can_resolve(ctx, (id.0, subst)) {
                    let tgt = resolve_opt(ctx.tcx, param_env, id.0, subst)
                        .unwrap_or_else(|| panic!("could not resolve {id:?} {subst:?}"));
                    let tgt = ctx.try_normalize_erasing_regions(param_env, tgt).unwrap_or(tgt);
                    Some(Dependency::Item(tgt.0.into(), tgt.1))
                } else {
                    let tgt = ctx.normalize_erasing_regions(param_env, (id, subst));
                    Some(Dependency::Item(tgt.0, tgt.1))
                };

                if let Some(tgt) = tgt {
                    self.add_edge(
                        ctx.tcx,
                        tgt,
                        Dependency::identity(ctx.tcx, id),
                        (lvl, EdgeType::Fake),
                    );
                    self.add_root(ctx, id);

                    self.add_edge(ctx.tcx, next, tgt, (lvl, EdgeType::Refinement(id, orig_subst)));

                    to_visit.push(tgt);
                }
            }
        }

        // Color the nodes
        for (src, tgt, (lvl, _)) in self.graph.all_edges() {
            debug!("{src:?} -> {tgt:?} at {lvl:?}");
            self.level.entry(tgt).and_modify(|a| *a = (*a).max(*lvl)).or_insert(*lvl);
        }
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = Dependency<'tcx>> + '_ {
        MonoGraphIter {
            walker: DfsPostOrder::empty(&self.graph),
            roots: self.roots.values().cloned(),
        }
        .iter(&self.graph)
    }

    fn add_edge(
        &mut self,
        tcx: TyCtxt<'tcx>,
        src: Dependency<'tcx>,
        tgt: Dependency<'tcx>,
        weight: (DepLevel, EdgeType<'tcx>),
    ) {
        let src = tcx.erase_regions(src);
        let tgt = tcx.erase_regions(tgt);

        if !self.graph.contains_edge(src, tgt) {
            self.graph.add_edge(src, tgt, weight);
        } else {
            let mut edge_weight = self.graph[(src, tgt)];

            // SKETCHY that this should work...
            // assert_eq!(edge_weight.1, weight.1, "{src:?} ->{tgt:?} ({weight:?})");

            edge_weight.0 = edge_weight.0.max(weight.0);
            edge_weight.1 = match (edge_weight.1, weight.1) {
                (EdgeType::Fake, b) => b,
                (EdgeType::Type, b) => b,
                (a, _b) => {
                    // assert_eq!(a, b);
                    a
                }
            };
            self.graph.update_edge(src, tgt, edge_weight);
        }
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
                self.walk_next(context)
            }
        }
    }
}

pub(crate) fn is_closure_hack<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: Id,
    subst: SubstsRef<'tcx>,
) -> Option<(Id, SubstsRef<'tcx>)> {
    if def_id.1.is_some() {
        return Some((def_id, subst));
    }

    debug!("is_closure_hack: {:?}", def_id);

    let self_ty = subst.types().nth(1);

    if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_precond"), def_id.0) {
        if let TyKind::Closure(id, csubst) = self_ty.unwrap().kind() {
            return Some((Id(*id, Some(ClosureId::Precondition)), csubst));
        }
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_once_impl_postcond"), def_id.0) {
        if let TyKind::Closure(id, csubst) = self_ty.unwrap().kind() {
            return Some((Id(*id, Some(ClosureId::PostconditionOnce)), csubst));
        }
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_postcond"), def_id.0) {
        if let TyKind::Closure(id, csubst) = self_ty.unwrap().kind() {
            return Some((Id(*id, Some(ClosureId::PostconditionMut)), csubst));
        }
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_impl_postcond"), def_id.0) {
        if let TyKind::Closure(id, csubst) = self_ty.unwrap().kind() {
            return Some((Id(*id, Some(ClosureId::Postcondition)), csubst));
        }
    } else if tcx.is_diagnostic_item(Symbol::intern("fn_mut_impl_unnest"), def_id.0) {
        if let TyKind::Closure(id, csubst) = self_ty.unwrap().kind() {
            return Some((Id(*id, Some(ClosureId::Unnest)), csubst));
        }
    };

    if tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_default"), def_id.0)
        || tcx.is_diagnostic_item(Symbol::intern("creusot_resolve_method"), def_id.0)
    {
        let self_ty = subst.types().nth(0).unwrap();
        if let TyKind::Closure(id, csubst) = self_ty.kind() {
            return Some((Id(*id, Some(ClosureId::Resolve)), csubst));
        }
    }

    None
}

fn can_resolve<'tcx>(ctx: &mut TranslationCtx<'tcx>, dep: (DefId, SubstsRef<'tcx>)) -> bool {
    ctx.trait_of_item(dep.0).is_some()
}

#[derive(Debug)]
pub struct Names<'tcx> {
    names: IndexMap<(Id, SubstsRef<'tcx>), Option<why3::Ident>>,
}

impl<'tcx> Names<'tcx> {
    pub(super) fn get(&self, tgt: (Id, SubstsRef<'tcx>)) -> Option<Option<why3::Ident>> {
        self.names.get(&tgt).cloned()
    }
}

pub(crate) fn name_clones<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    graph: &MonoGraph<'tcx>,
    root: Dependency<'tcx>,
) -> Names<'tcx> {
    let mut names: IndexMap<(Id, _), _> = IndexMap::new();
    let mut assigned = IndexMap::new();
    let walk = DfsPostOrder::new(&graph.graph, root);

    let root_id = root.as_item().unwrap().0;
    for node in walk.iter(&graph.graph) {
        let Dependency::Item(def_id, subst) = node else { continue };

        let clone_name: Option<why3::Ident> = if ctx.is_closure(root_id.0) && root_id == def_id {
            None
        } else if !ctx.is_closure(root_id.0) && ctx.binding_group(root_id.0).contains(&def_id.0) {
            None
        } else {
            let base_sym = match util::item_type(ctx.tcx, def_id.0) {
                ItemType::Impl => ctx.item_name(ctx.trait_id_of_impl(def_id.0).unwrap()),
                ItemType::Closure => Symbol::intern(&format!(
                    "closure{}",
                    ctx.def_path(def_id.0).data.last().unwrap().disambiguator
                )),
                _ => Symbol::intern(&*util::item_name(ctx.tcx, def_id.0, Namespace::ValueNS)),
            };
            let count = assigned.entry(base_sym).and_modify(|c| *c += 1).or_insert(0);

            Some(format!("{}{}", base_sym.as_str().to_upper_camel_case(), count).into())
        };

        names.insert((def_id, subst), clone_name);
    }

    Names { names }
}

// Temporary, eventually provided via a cached query
// A map of the public clones in each definition
pub struct PriorClones<'a, 'tcx> {
    prior: IndexMap<Id, Names<'tcx>>,
    graph: &'a MonoGraph<'tcx>,
}

#[derive(Clone, Copy)]
pub struct Namer<'a, 'tcx> {
    priors: &'a PriorClones<'a, 'tcx>,
    id: Id,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> Namer<'a, 'tcx> {
    fn ident(&mut self, def_id: Id, subst: SubstsRef<'tcx>) -> Option<why3::Ident> {
        let (def_id, subst) = self.tcx.erase_regions((def_id, subst));
        self.priors
            .prior
            .get(&self.id)
            .unwrap_or_else(|| panic!("no names for {:?}", self.id))
            .get((def_id, subst))
            .unwrap_or_else(|| {
                self.priors.prior.get(&self.id).unwrap().names.iter().for_each(|k| {
                    // if self.tcx.def_path_str(k.0.0).contains("collect") {
                    eprintln!("{k:?}");
                    // }
                });
                // eprintln!("{:?}", self.priors.prior.get(&self.id).unwrap());
                panic!("Could not find ({:?},{:?}) in dependencies of {:?}", def_id, subst, self.id)
            })
    }
}

impl<'tcx> Cloner<'tcx> for Namer<'_, 'tcx> {
    fn value(&mut self, def_id: Id, subst: SubstsRef<'tcx>) -> QName {
        if let Some(b) = get_builtin(self.tcx, def_id.0) {
            return QName::from_string(&b.as_str()).unwrap().without_search_path();
        }

        let base = self.ident(def_id, subst);
        QName {
            module: base.into_iter().collect(),
            name: item_name(self.tcx, def_id.0, Namespace::ValueNS),
        }
    }

    fn ty(&mut self, def_id: Id, subst: SubstsRef<'tcx>) -> QName {
        let base = self.ident(def_id, subst);
        QName {
            module: base.into_iter().collect(),
            name: item_name(self.tcx, def_id.0, Namespace::TypeNS),
        }
    }

    fn accessor(&mut self, def_id: Id, subst: SubstsRef<'tcx>, variant: usize, ix: usize) -> QName {
        if util::item_type(self.tcx, def_id.0) == ItemType::Closure {
            let id = Id(def_id.0, Some(ClosureId::Type));
            QName {
                module: self.ident(id, subst).into_iter().collect(),
                name: format!("field_{}", ix).into(),
            }
        } else {
            let field = &self.tcx.adt_def(def_id.0).variants()[variant.into()].fields[ix];
            let base = self.ident(field.did.into(), subst);

            QName {
                module: base.into_iter().collect(),
                name: item_name(self.tcx, field.did, Namespace::ValueNS),
            }
        }
    }

    fn constructor(&mut self, def_id: Id, subst: SubstsRef<'tcx>, variant: usize) -> QName {
        let variant_id = match util::item_type(self.tcx, def_id.0) {
            ItemType::Closure => def_id.0,
            ItemType::Type => self.tcx.adt_def(def_id.0).variants()[variant.into()].def_id,
            _ => unreachable!(),
        };
        let base = self.ident(def_id, subst);
        let mut name = item_name(self.tcx, variant_id, Namespace::ValueNS);
        name.capitalize();
        QName { module: base.into_iter().collect(), name }
    }

    fn to_clones(
        &mut self,
        ctx: &mut TranslationCtx<'tcx>,
        vis: CloneVisibility,
        depth: CloneDepth,
    ) -> Vec<Decl> {
        make_clones(ctx, *self, vis, depth, self.id)
    }
}

impl<'a, 'tcx> PriorClones<'a, 'tcx> {
    pub(crate) fn from_graph(ctx: &mut TranslationCtx<'tcx>, graph: &'a MonoGraph<'tcx>) -> Self {
        let mut clones = IndexMap::new();

        for node in graph.roots.values() {
            let Dependency::Item(def_id, _) = node else { continue };

            if !clones.contains_key(def_id) {
                clones.insert(*def_id, name_clones(ctx, graph, *node));
            }
        }

        PriorClones { graph, prior: clones }
    }

    #[allow(dead_code)]
    pub(crate) fn debug(&self, tcx: TyCtxt<'tcx>) {
        println!(
            "{:?}",
            Dot::with_attr_getters(
                &self.graph.graph,
                &[Config::EdgeNoLabel, Config::NodeNoLabel],
                &|_, (src, tgt, (_, typ))| {
                    let x = if let Some((id, _)) = src.as_item() &&
                    let Some((tgt, subst)) = tgt.as_item() &&
                        let Some(Some(idnt)) = self.prior[&Id::from(id)].get((tgt.into(), subst)) {
                        idnt.to_string()
                    } else {
                        String::new()
                    };

                    let color = match typ {
                        EdgeType::Refinement(_, _) => "black",
                        EdgeType::Fake => "green",
                        EdgeType::Type => "blue",
                    };
                    format!("label = \"{x}\", color=\"{color}\"")
                },
                &|_, n| {
                    match n.0 {
                        Dependency::Item(id, s) => {
                            let name = if let Some(i) = tcx.opt_item_name(id.0) {
                                format!("{}", i)
                            } else {
                                if let Some(cid) = id.1 {
                                    format!("closure({})", cid.name())
                                } else {
                                    format!("closure")
                                }
                            };
                            format!("label = \"{}, {}\"", name, format!("{:?}", s).escape_debug())
                        }
                        Dependency::BaseTy(ty) => format!("label = \"{:?}\"", ty),
                    }
                }
            )
        );
    }

    pub(crate) fn get(&'a self, tcx: TyCtxt<'tcx>, inside: Id) -> Namer<'a, 'tcx> {
        Namer { priors: self, id: inside, tcx }
    }
}

fn identity_substs_for<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> SubstsRef<'tcx> {
    if tcx.is_closure(def_id) {
        match tcx.type_of(def_id).kind() {
            TyKind::Closure(_, subst) => return subst,
            _ => unreachable!(),
        }
    };

    InternalSubsts::identity_for_item(tcx, def_id)
}

// Transform a graph into a set of clones
pub(crate) fn make_clones<'tcx, 'a>(
    ctx: &mut TranslationCtx<'tcx>,
    priors: Namer<'a, 'tcx>,
    vis: CloneVisibility,
    depth: CloneDepth,
    root_id: Id,
) -> Vec<Decl> {
    let Namer { priors, .. } = priors;
    let mut names = priors.get(ctx.tcx, root_id);
    let root = Dependency::identity(ctx.tcx, root_id);
    let mut topo = DfsPostOrder::new(&priors.graph.graph, root);

    // Unify
    let desired_dep_level = match vis {
        CloneVisibility::Interface => DepLevel::Signature,
        CloneVisibility::Body => DepLevel::Body,
    };

    let mut clones = Vec::new();
    let mut uses = IndexSet::new();

    let fgraph =
        EdgeFiltered::from_fn(&priors.graph.graph, |(_, _, (_, ek))| ek != &EdgeType::Fake);
    while let Some(node) = topo.walk_next(&fgraph) {
        if node == root {
            continue;
        }

        if priors.graph.level[&node] < desired_dep_level {
            continue;
        };

        let (id, subst) = match node {
            Dependency::Item(id, subst) => (id, subst),
            Dependency::BaseTy(ty) => {
                if let Some(nm) = base_ty_name(ty) {
                    uses.insert(Use { name: nm, as_: None });
                }
                continue;
            }
        };

        if !ctx.is_closure(root_id.0) && ctx.binding_group(root_id.0).contains(&id.0) {
            continue;
        }

        if let Some(builtin) = get_builtin(ctx.tcx, id.0) {
            let name = QName::from_string(&builtin.as_str()).unwrap().module_qname();
            uses.insert(Use { name: name.clone(), as_: None });
            continue;
        };

        if matches!(item_type(ctx.tcx, id.0), ItemType::Type) {
            let name = item_qname(ctx, id.0, Namespace::TypeNS).module_qname();
            let as_name = names.value(id, subst).module_ident().unwrap().clone();
            uses.insert(Use { name: name.clone(), as_: Some(as_name) });

            continue;
        };

        let mut clone_subst = base_subst(ctx, names, id.0, subst);

        let mut node_names = priors.get(ctx.tcx, id);

        // if ctx.item_name(root_id.0).as_str().contains("next") && ctx.item_name(id.0).as_str().contains("produces") {
        //     eprintln!("{:?} {:?}", root_id.0, id.0);
        // }

        // if ctx.item_name(root_id.0).as_str() == ("into_iter") {
        //     eprintln!("{:?} {:?}", root_id.0, id.0);
        //     eprintln!(
        //         "{:?}",
        //         priors.graph.graph.neighbors_directed(node, Outgoing).collect::<Vec<_>>()
        //     );
        // }
        for dep in priors.graph.graph.neighbors_directed(node, Outgoing) {
            if priors.graph.level[&dep] < desired_dep_level {
                continue;
            };

            if dep == node {
                continue;
            };

            // TODO: introduce a notion of opacity to address this
            if item_type(ctx.tcx, id.0) == ItemType::Program
                && priors.graph.level[&dep] == DepLevel::Body
            {
                continue;
            }

            let (_, orig) = priors.graph.graph[(node, dep)];

            // if ctx.item_name(root_id.0).as_str() == ("into_iter") {
            //     eprintln!("Depdency {dep:?} orig {orig:?}");
            // }

            let EdgeType::Refinement(orig_id, orig_subst) = orig else { continue };

            if depth == CloneDepth::Shallow && item_type(ctx.tcx, orig_id.0) != ItemType::AssocTy {
                continue;
            }

            // // FIXME: Not really correct
            if item_type(ctx.tcx, orig_id.0) == ItemType::Type {
                continue;
            }

            if get_builtin(ctx.tcx, orig_id.0).is_some() {
                continue;
            };

            let src = node_names.value(orig_id, orig_subst);
            let tgt = dep.as_item().map(|(id, subst)| names.value(id.into(), subst));

            let sub = match item_type(ctx.tcx, orig_id.0) {
                ItemType::Logic => CloneSubst::Function(src, tgt.unwrap()),
                ItemType::Predicate => CloneSubst::Predicate(src, tgt.unwrap()),
                ItemType::Constant => CloneSubst::Val(src, tgt.unwrap()),
                ItemType::AssocTy => CloneSubst::Type(
                    src,
                    translate_ty(ctx, &mut names, DUMMY_SP, dep.as_ty(ctx.tcx)),
                ),
                _ => CloneSubst::Val(src, tgt.unwrap()),
            };
            clone_subst.push(sub)
        }

        let clone = DeclClone {
            name: cloneable_name(ctx, id, depth),
            subst: clone_subst,
            kind: CloneKind::Named(names.value(id, subst).module_ident().unwrap().clone()),
        };

        clones.push(Decl::Clone(clone));
    }

    uses.into_iter().map(Decl::UseDecl).chain(clones).collect()
}

fn base_ty_name(ty: Ty) -> Option<QName> {
    match ty.kind() {
        TyKind::Bool => QName::from_string("prelude.Bool"),
        TyKind::Char => QName::from_string("prelude.Char"),
        TyKind::Int(IntTy::I8) => QName::from_string("prelude.Int8"),
        TyKind::Int(IntTy::I16) => QName::from_string("prelude.Int16"),
        TyKind::Int(IntTy::I32) => QName::from_string("mach.int.Int32"),
        TyKind::Int(IntTy::I64) => QName::from_string("mach.int.Int64"),
        TyKind::Int(IntTy::I128) => QName::from_string("prelude.Int128"),
        TyKind::Uint(UintTy::U8) => QName::from_string("prelude.UInt8"),
        TyKind::Uint(UintTy::U16) => QName::from_string("prelude.UInt16"),
        TyKind::Uint(UintTy::U32) => QName::from_string("mach.int.UInt32"),
        TyKind::Uint(UintTy::U64) => QName::from_string("mach.int.UInt64"),
        TyKind::Uint(UintTy::U128) => QName::from_string("prelude.UInt128"),
        TyKind::Int(IntTy::Isize) => QName::from_string("prelude.IntSize"),
        TyKind::Uint(UintTy::Usize) => QName::from_string("prelude.UIntSize"),
        TyKind::Float(FloatTy::F32) => QName::from_string("ieee_float.Float32"),
        TyKind::Float(FloatTy::F64) => QName::from_string("ieee_float.Float64"),
        TyKind::Str => todo!(),
        TyKind::Slice(_) => QName::from_string("prelude.Slice"),
        TyKind::RawPtr(_) => QName::from_string("prelude.Opaque"),
        TyKind::Ref(_, _, _) => QName::from_string("prelude.Borrow"),
        TyKind::Never => None,
        TyKind::Tuple(_) => None,
        TyKind::Array(_, _) => QName::from_string("seq.Seq"),
        _ => None,
    }
}
// PreludeModule::Int => QName::from_string("mach.int.Int").unwrap(),
// PreludeModule::Opaque => QName::from_string("prelude.Opaque").unwrap(),
// PreludeModule::Ref => QName::from_string("Ref").unwrap(),
// PreludeModule::Seq => QName::from_string("seq.Seq").unwrap(),

pub(crate) fn base_subst<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    mut names: Namer<'_, 'tcx>,
    mut def_id: DefId,
    subst: SubstsRef<'tcx>,
) -> Vec<CloneSubst> {
    use creusot_rustc::middle::ty::GenericParamDefKind;
    use heck::ToSnakeCase;
    loop {
        if ctx.is_closure(def_id) {
            def_id = ctx.parent(def_id);
        } else {
            break;
        }
    }
    let trait_params = ctx.generics_of(def_id);
    let mut clone_subst = Vec::new();

    if subst.is_empty() {
        return Vec::new();
    }

    for ix in 0..trait_params.count() {
        let p = trait_params.param_at(ix, ctx.tcx);
        let ty = subst[ix];
        if let GenericParamDefKind::Type { .. } = p.kind {
            let ty = translate_ty(ctx, &mut names, DUMMY_SP, ty.expect_ty());
            clone_subst.push(CloneSubst::Type(p.name.to_string().to_snake_case().into(), ty));
        }
    }

    clone_subst
}

// Which kind of module should we clone
// TODO: Unify with `CloneOpacity`
#[derive(Copy, Clone, PartialEq, Eq)]
pub enum CloneVisibility {
    Interface,
    Body,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum CloneDepth {
    Shallow,
    Deep,
}

pub(super) fn cloneable_name(ctx: &TranslationCtx, def_id: Id, interface: CloneDepth) -> QName {
    use util::ItemType::*;

    // TODO: Refactor.
    match util::item_type(ctx.tcx, def_id.0) {
        Logic | Predicate | Impl | Constant | Field => match interface {
            CloneDepth::Shallow => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx, def_id.0)).into(),
            },
            CloneDepth::Deep => module_name(ctx, def_id.0).into(),
        },

        Program => QName {
            module: Vec::new(),
            name: format!("{}_Stub", &*module_name(ctx, def_id.0)).into(),
        },
        Closure => match def_id.1 {
            Some(ClosureId::Type) => QName {
                module: Vec::new(),
                name: format!("{}_Type", &*module_name(ctx, def_id.0)).into(),
            },
            Some(ClosureId::Resolve)
            | Some(ClosureId::Unnest)
            | Some(ClosureId::Precondition)
            | Some(ClosureId::Postcondition)
            | Some(ClosureId::PostconditionOnce)
            | Some(ClosureId::Field)
            | Some(ClosureId::PostconditionMut) => match interface {
                CloneDepth::Shallow => QName {
                    module: Vec::new(),
                    name: format!(
                        "{}_{}_Stub",
                        &*module_name(ctx, def_id.0),
                        def_id.1.unwrap().name()
                    )
                    .into(),
                },
                CloneDepth::Deep => module_name(ctx, def_id.0).into(),
            },
            None => QName {
                module: Vec::new(),
                name: format!("{}_Stub", &*module_name(ctx, def_id.0)).into(),
            },
        },
        Trait | Type | AssocTy => module_name(ctx, def_id.0).into(),
        // Field => panic!(),
        Unsupported(_) => unreachable!(),
    }
}

// Walk all the projections in a substitution so we can add dependencies on them
fn walk_projections<'tcx, T: TypeFoldable<'tcx>, F: FnMut(Ty<'tcx>)>(s: T, f: F) {
    s.visit_with(&mut ProjectionTyVisitor { f, p: std::marker::PhantomData });
}

struct ProjectionTyVisitor<'tcx, F: FnMut(Ty<'tcx>)> {
    f: F,
    p: std::marker::PhantomData<&'tcx ()>,
}

impl<'tcx, F: FnMut(Ty<'tcx>)> TypeVisitor<'tcx> for ProjectionTyVisitor<'tcx, F> {
    fn visit_ty(&mut self, t: Ty<'tcx>) -> std::ops::ControlFlow<Self::BreakTy> {
        match t.kind() {
            TyKind::Projection(_pty) => {
                (self.f)(t);
                t.super_visit_with(self)
            }
            _ => t.super_visit_with(self),
        }
    }
}
