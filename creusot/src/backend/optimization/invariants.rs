//! fMIR transformations
//!
//! This module defines a fMIR transformation which analyzes the body for
//! 1- Places or prophecies of places that are unchanged during loops.

use std::assert_matches::assert_matches;

use crate::{
    backend::{
        program::node_graph,
        projections::iter_projections_ty,
        ty::{AdtKind, classify_adt},
        wto::{Component, weak_topological_order},
    },
    ctx::TranslationCtx,
    translation::{
        fmir::{
            Block, Body, FmirVisitor, Invariant, LocalDecl, Operand, Place, ProjectionElem, RValue,
            Statement, StatementKind, Terminator,
        },
        pearlite::{Ident, Term},
    },
};
use indexmap::{IndexMap, map::Entry};
use itertools::Itertools;
use petgraph::Direction;
use rustc_abi::FieldIdx;
use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{BasicBlock, PlaceTy, START_BLOCK},
    ty::{Ty, TyKind},
};
use rustc_span::DUMMY_SP;

/// Add loop invariants to `body` for each mutable borrow that is _not_ modified in a loop.
pub(crate) fn infer_invariant_places<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &mut Body<'tcx>,
    scope: DefId,
) {
    let graph = node_graph(body);

    let wto = weak_topological_order(&graph, START_BLOCK);
    let dates = traverse_wto(&wto);

    for (k, unchanged) in unchanged_places_analysis(ctx, body, scope, &wto).into_iter() {
        for u in unchanged {
            let local = Ident::fresh_local("_old");
            body.locals
                .insert(local, LocalDecl { span: DUMMY_SP, ty: u.ty, temp: true, arg: false });

            for p in
                graph.neighbors_directed(k, Direction::Incoming).filter(|p| dates[p] > dates[&k])
            {
                let mut prev_block = body.blocks.get_mut(&p).unwrap();
                if let Terminator::Switch(_, branches) = &mut prev_block.terminator {
                    let new_block = BasicBlock::from(body.fresh);
                    body.fresh += 1;
                    for tgt in branches.targets_mut().filter(|tgt| **tgt == k) {
                        *tgt = new_block;
                    }
                    body.blocks.insert(
                        new_block,
                        Block {
                            invariants: vec![],
                            variant: None,
                            stmts: vec![],
                            terminator: Terminator::Goto(k),
                        },
                    );
                    prev_block = body.blocks.get_mut(&new_block).unwrap();
                }
                assert_matches!(prev_block.terminator, Terminator::Goto(t) if t == k);
                prev_block.stmts.push(Statement {
                    kind: StatementKind::Assignment(
                        Place { local, projection: Box::new([]) },
                        RValue::Operand(Operand::term(u.clone())),
                    ),
                    span: body.block_spans[&p],
                });
            }

            let blk = body.blocks.get_mut(&k).unwrap();
            blk.invariants.insert(
                0,
                Invariant {
                    body: Term::var(local, u.ty).eq(ctx.tcx, u),
                    expl: "expl:mut invariant".to_string(),
                },
            );
        }
    }
}

fn traverse_wto(comps: &[Component<BasicBlock>]) -> IndexMap<BasicBlock, u32> {
    fn inner(e: &mut IndexMap<BasicBlock, u32>, date: &mut u32, comps: &[Component<BasicBlock>]) {
        for comp in comps.iter().rev() {
            let bb = match comp {
                &Component::Simple(bb) => bb,
                &Component::Complex(bb, ref members) => {
                    inner(e, date, members);
                    bb
                }
            };
            e.insert(bb, *date);
            *date += 1;
        }
    }
    let mut result = IndexMap::new();
    inner(&mut result, &mut 0, comps);
    result
}

enum ChangedPlacesTree {
    Changed,
    DerefBox(Box<ChangedPlacesTree>),
    DerefRefMut(Box<ChangedPlacesTree>),
    Fields(IndexVec<FieldIdx, Option<ChangedPlacesTree>>),
}

impl ChangedPlacesTree {
    fn to_unchanged_term_vec<'tcx>(
        &self,
        ctx: &TranslationCtx<'tcx>,
        scope: DefId,
        t: Term<'tcx>,
        acc: &mut Vec<Term<'tcx>>,
    ) {
        match self {
            Self::Changed => (),
            Self::DerefBox(c) => c.to_unchanged_term_vec(ctx, scope, t.deref(), acc),
            Self::DerefRefMut(c) => {
                acc.push(t.clone().fin());
                c.to_unchanged_term_vec(ctx, scope, t.cur(), acc);
            }
            Self::Fields(c) => match t.ty.kind() {
                TyKind::Closure(_, subst) => {
                    for ((idx, c), ty) in c.iter_enumerated().zip_eq(subst.as_closure().upvar_tys())
                    {
                        if let Some(c) = c {
                            c.to_unchanged_term_vec(ctx, scope, t.clone().proj(idx, ty), acc);
                        } else {
                            acc.push(t.clone().proj(idx, ty));
                        }
                    }
                }
                TyKind::Tuple(tys) => {
                    for ((idx, c), ty) in c.iter_enumerated().zip_eq(tys.iter()) {
                        if let Some(c) = c {
                            c.to_unchanged_term_vec(ctx, scope, t.clone().proj(idx, ty), acc);
                        } else {
                            acc.push(t.clone().proj(idx, ty));
                        }
                    }
                }
                TyKind::Adt(def, subst) => {
                    let AdtKind::Struct { .. } = classify_adt(ctx, scope, *def, subst) else {
                        unreachable!()
                    };
                    for ((idx, fdef), c) in
                        def.non_enum_variant().fields.iter_enumerated().zip_eq(c)
                    {
                        let ty = fdef.ty(ctx.tcx, subst);
                        if let Some(c) = c {
                            c.to_unchanged_term_vec(ctx, scope, t.clone().proj(idx, ty), acc);
                        } else if fdef.vis.is_accessible_from(scope, ctx.tcx) {
                            acc.push(t.clone().proj(idx, ty));
                        }
                    }
                }
                _ => unreachable!(),
            },
        }
    }

    fn record_write<'tcx>(
        ctx: &TranslationCtx<'tcx>,
        proj: &[ProjectionElem<'tcx>],
        ty: Ty<'tcx>,
    ) -> Self {
        let mut res = Self::Changed;
        for (elem, place_ty) in iter_projections_ty(ctx, proj, &mut PlaceTy::from_ty(ty))
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
        {
            match elem {
                ProjectionElem::Deref => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) if def.is_box() => res = Self::DerefBox(Box::new(res)),
                    TyKind::Ref(_, _, Mutability::Mut) => res = Self::DerefRefMut(Box::new(res)),
                    _ => unreachable!(),
                },
                ProjectionElem::Field(idx, _) => {
                    let n = match place_ty.ty.kind() {
                        TyKind::Closure(_, subst) => subst.as_closure().upvar_tys().len(),
                        TyKind::Tuple(tys) => tys.len(),
                        TyKind::Adt(def, _) if def.is_struct() => {
                            def.non_enum_variant().fields.len()
                        }
                        _ => {
                            res = Self::Changed;
                            continue;
                        }
                    };
                    let mut v = IndexVec::from_fn_n(|_| None, n);
                    v[*idx] = Some(res);
                    res = Self::Fields(v)
                }
                _ => res = Self::Changed,
            }
        }
        res
    }

    fn merge(&mut self, t: Self) {
        match (self, t) {
            (Self::Changed, _) => (),
            (s, Self::Changed) => *s = Self::Changed,
            (Self::DerefBox(box s), Self::DerefBox(box t))
            | (Self::DerefRefMut(box s), Self::DerefRefMut(box t)) => s.merge(t),
            (Self::Fields(flds), Self::Fields(fldt)) => {
                for (s, t) in flds.iter_mut().zip_eq(fldt) {
                    match (s, t) {
                        (_, None) => (),
                        (s @ None, t) => *s = t,
                        (Some(s), Some(t)) => s.merge(t),
                    }
                }
            }
            _ => unreachable!(),
        }
    }

    fn merge_in_entry<K>(self, e: Entry<K, ChangedPlacesTree>) {
        match e {
            Entry::Occupied(mut e) => e.get_mut().merge(self),
            Entry::Vacant(e) => {
                e.insert(self);
            }
        }
    }
}

struct UnchangedPlaces<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    body: &'a Body<'tcx>,
    scope: DefId,
    writes: IndexMap<Ident, ChangedPlacesTree>,
    unchanged: &'a mut IndexMap<BasicBlock, Vec<Term<'tcx>>>,
}

impl<'a, 'tcx> UnchangedPlaces<'a, 'tcx> {
    fn initialize(
        ctx: &'a TranslationCtx<'tcx>,
        body: &'a Body<'tcx>,
        scope: DefId,
        unchanged: &'a mut IndexMap<BasicBlock, Vec<Term<'tcx>>>,
    ) -> Self {
        Self { ctx, body, scope, writes: Default::default(), unchanged }
    }

    fn record_write_to(&mut self, pl: &Place<'tcx>) {
        let t = ChangedPlacesTree::record_write(
            self.ctx,
            &pl.projection,
            self.body.locals[&pl.local].ty,
        );
        t.merge_in_entry(self.writes.entry(pl.local))
    }
}

impl<'tcx> FmirVisitor<'tcx> for UnchangedPlaces<'_, 'tcx> {
    fn visit_stmt(&mut self, stmt: &Statement<'tcx>) {
        match &stmt.kind {
            StatementKind::Assignment(l, r) => {
                self.record_write_to(l);
                if let RValue::Borrow(_, r) = r {
                    self.record_write_to(r);
                }
            }
            StatementKind::Call(r, _, _, _, _) => self.record_write_to(r),
            _ => (),
        }
    }
}

fn unchanged_places_analysis_inner<'a, 'tcx>(
    state_parent: &mut UnchangedPlaces<'a, 'tcx>,
    c: &Component<BasicBlock>,
) {
    match c {
        Component::Simple(b) => state_parent.visit_block(&state_parent.body.blocks[b]),
        Component::Complex(h, l) => {
            let mut state = UnchangedPlaces::initialize(
                state_parent.ctx,
                &state_parent.body,
                state_parent.scope,
                state_parent.unchanged,
            );
            state.visit_block(&state_parent.body.blocks[h]);

            for b in l {
                unchanged_places_analysis_inner(&mut state, b)
            }

            let mut unchanged_here = vec![];
            for (l, t) in state.writes {
                t.to_unchanged_term_vec(
                    state.ctx,
                    state.scope,
                    Term::var(l, state.body.locals[&l].ty),
                    &mut unchanged_here,
                );
                t.merge_in_entry(state_parent.writes.entry(l));
            }

            state_parent.unchanged.insert(*h, unchanged_here);
        }
    }
}

fn unchanged_places_analysis<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &Body<'tcx>,
    scope: DefId,
    c: &[Component<BasicBlock>],
) -> IndexMap<BasicBlock, Vec<Term<'tcx>>> {
    let mut unchanged = Default::default();
    let mut state = UnchangedPlaces::initialize(ctx, body, scope, &mut unchanged);

    for comp in c {
        unchanged_places_analysis_inner(&mut state, comp);
    }

    unchanged
}
