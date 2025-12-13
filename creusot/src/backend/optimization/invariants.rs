//! fMIR transformations
//!
//! This module defines a fMIR transformation which analyzes the body for
//! 1- Places or prophecies of places that are unchanged during loops.

use crate::{
    backend::{
        program::node_graph,
        projections::{iter_projections_ty, projections_term},
        ty::{AdtKind, classify_adt},
        ty_inv::{inv_call, is_tyinv_trivial, resolve_user_inv},
        wto::{Component, weak_topological_order},
    },
    contracts_items::is_open_inv_result,
    ctx::TranslationCtx,
    translation::{
        fmir::{
            Block, Body, Invariant, LocalDecl, LocalKind, Operand, Place, ProjectionElem, RValue,
            Statement, StatementKind, Terminator,
        },
        pearlite::{Ident, Term},
        traits::TraitResolved,
    },
};
use indexmap::{IndexMap, map::Entry};
use itertools::Itertools;
use petgraph::Direction;
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_ast::Mutability;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::{
    mir::{BasicBlock, PlaceTy, START_BLOCK},
    ty::{Ty, TyKind, TypingEnv},
};
use rustc_span::DUMMY_SP;
use std::{assert_matches::assert_matches, iter::repeat, ops::Deref};

struct InvariantAnalysisCtx<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    body: &'a Body<'tcx>,
    scope: DefId,
    typing_env: TypingEnv<'tcx>,
}

impl<'a, 'tcx> Deref for InvariantAnalysisCtx<'a, 'tcx> {
    type Target = TranslationCtx<'tcx>;

    fn deref(&self) -> &TranslationCtx<'tcx> {
        return &self.ctx;
    }
}

/// Add loop invariants to `body` for each mutable borrow that is _not_ modified in a loop.
pub(crate) fn infer_invariant<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &mut Body<'tcx>,
    scope: DefId,
    typing_env: TypingEnv<'tcx>,
) {
    let graph = node_graph(body);

    let wto = weak_topological_order(&graph, START_BLOCK);
    let dates = traverse_wto(&wto);

    let actx = InvariantAnalysisCtx { ctx, body, scope, typing_env };
    let unchanged_analysis = changed_places_analysis(&actx, &wto);
    let ini_state = TyInvState(
        body.locals
            .iter()
            .filter_map(|(&l, ld)| {
                (ld.kind == LocalKind::Param { open_inv: false }
                    && !is_tyinv_trivial(ctx, scope, typing_env, ld.ty, DUMMY_SP))
                .then_some((l, TyInvPlacesTree::TyInv))
            })
            .collect(),
    );
    let mut ty_inv_analysis_states = IndexMap::from([(START_BLOCK, ini_state)]);
    ty_inv_analysis(&actx, &wto, &mut ty_inv_analysis_states);

    for (k, changed) in unchanged_analysis {
        let mut unchanged_trms = vec![];
        for (&l, t) in changed.0.iter() {
            let trm = Term::var(l, body.locals[&l].ty);
            t.to_unchanged_term_vec(ctx, scope, trm, &mut unchanged_trms);
        }

        for u in unchanged_trms {
            let local = Ident::fresh_local("_old");
            body.locals
                .insert(local, LocalDecl { span: DUMMY_SP, ty: u.ty, kind: LocalKind::Temp });

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

            let inv = Term::var(local, u.ty).eq(ctx.tcx, u);

            body.blocks.get_mut(&k).unwrap().invariants.insert(
                0,
                Invariant { inv, expl: "expl:inferred invariant: unchanged value".to_string() },
            );
        }

        let ty_inv_places = ty_inv_analysis_states
            .swap_remove(&k)
            .unwrap_or_default()
            .to_tyinv_place_vec(&changed, ctx, body);
        for pl in ty_inv_places {
            let inv = projections_term(
                ctx,
                typing_env,
                Term::var(pl.local, body.locals[&pl.local].ty),
                &pl.projection,
                |x| inv_call(ctx, typing_env, scope, x).unwrap(),
                Some(Term::true_(ctx.tcx)),
                |id| Term::var(*id, ctx.types.usize),
                DUMMY_SP,
            );

            body.blocks.get_mut(&k).unwrap().invariants.insert(
                0,
                Invariant { inv, expl: "expl:inferred invariant: type invariant".to_string() },
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

#[derive(Clone, Debug)]
enum ChangedPlacesTree {
    Changed,
    Deref(Box<ChangedPlacesTree>),
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
            Self::Deref(c) => {
                if let TyKind::Ref(_, _, Mutability::Mut) = t.ty.kind() {
                    acc.push(t.clone().fin())
                }
                c.to_unchanged_term_vec(ctx, scope, t.deref(), acc);
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
        ctx: &InvariantAnalysisCtx<'_, 'tcx>,
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
                ProjectionElem::Deref => res = Self::Deref(Box::new(res)),
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
            (Self::Deref(box s), Self::Deref(box t)) => s.merge(t),
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

#[derive(Default)]
struct ChangedPlaces(IndexMap<Ident, ChangedPlacesTree>);

impl ChangedPlaces {
    fn record_write_to<'tcx>(&mut self, ctx: &InvariantAnalysisCtx<'_, 'tcx>, pl: &Place<'tcx>) {
        let t = ChangedPlacesTree::record_write(ctx, &pl.projection, ctx.body.locals[&pl.local].ty);
        t.merge_in_entry(self.0.entry(pl.local))
    }

    fn record_block_writes<'tcx>(
        &mut self,
        ctx: &InvariantAnalysisCtx<'_, 'tcx>,
        block: &Block<'tcx>,
    ) {
        for stmt in &block.stmts {
            match &stmt.kind {
                StatementKind::Assignment(l, _) => self.record_write_to(ctx, l),
                StatementKind::MutBorrow(_, l, r) => {
                    self.record_write_to(ctx, l);
                    self.record_write_to(ctx, r);
                }
                StatementKind::Call(r, _, _, _, _) => self.record_write_to(ctx, r),
                _ => (),
            }
        }
    }
}

fn changed_places_analysis<'tcx>(
    ctx: &InvariantAnalysisCtx<'_, 'tcx>,
    c: &[Component<BasicBlock>],
) -> IndexMap<BasicBlock, ChangedPlaces> {
    fn inner<'a, 'tcx>(
        ctx: &InvariantAnalysisCtx<'_, 'tcx>,
        states: &mut IndexMap<BasicBlock, ChangedPlaces>,
        state_parent: &mut ChangedPlaces,
        c: &[Component<BasicBlock>],
    ) {
        for comp in c {
            match comp {
                Component::Simple(b) => state_parent.record_block_writes(ctx, &ctx.body.blocks[b]),
                Component::Complex(h, l) => {
                    let mut state = ChangedPlaces::default();
                    state_parent.record_block_writes(ctx, &ctx.body.blocks[h]);
                    inner(ctx, states, &mut state, l);
                    for (l, t) in &state.0 {
                        t.clone().merge_in_entry(state_parent.0.entry(*l));
                    }
                    states.insert(*h, state);
                }
            }
        }
    }

    let mut res = Default::default();
    let mut state = ChangedPlaces::default();
    inner(ctx, &mut res, &mut state, c);
    res
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TyInvPlacesTree {
    /// Convention: places for which the tyinv is trivial have the `Top` abstract value
    TyInv,
    Deref(Box<TyInvPlacesTree>),
    Fields(IndexVec<FieldIdx, TyInvPlacesTree>),
    Downcasts(IndexVec<VariantIdx, TyInvPlacesTree>),
    /// Only used for temporaries and in `Fields` and `Downcasts` constructors
    Top,
}

impl TyInvPlacesTree {
    fn join(&mut self, other: &Self) {
        match (self, other) {
            (Self::Top, _) | (_, Self::TyInv) => (),
            (s, Self::Top) => *s = Self::Top,
            (s @ Self::TyInv, other) => *s = other.clone(),
            (Self::Deref(box s), Self::Deref(box o)) => s.join(o),
            (Self::Fields(flds), Self::Fields(fldo)) => {
                for (s, o) in flds.iter_mut().zip_eq(fldo) {
                    s.join(o)
                }
            }
            (Self::Downcasts(vs), Self::Downcasts(vo)) => {
                for (s, o) in vs.iter_mut().zip_eq(vo) {
                    s.join(o)
                }
            }
            _ => unreachable!(),
        }
    }

    fn write<'a, 'tcx: 'a>(
        &mut self,
        ctx: &InvariantAnalysisCtx<'_, 'tcx>,
        mut it: impl Iterator<Item = (&'a ProjectionElem<'tcx>, PlaceTy<'tcx>)>,
        leaf: Self,
    ) {
        let is_tyinv_trivial = |ty| is_tyinv_trivial(ctx, ctx.scope, ctx.typing_env, ty, DUMMY_SP);
        let Some((elem, place_ty)) = it.next() else {
            *self = leaf;
            return;
        };

        match elem {
            ProjectionElem::Deref => {
                if let Self::TyInv = self {
                    *self = Self::Deref(Box::new(Self::TyInv))
                } else if let Self::Top = self {
                    *self = Self::Deref(Box::new(Self::Top))
                }

                let Self::Deref(box s) = self else { unreachable!() };
                s.write(ctx, it, leaf);

                if let Self::TyInv = s {
                    *self = Self::TyInv
                } else if let Self::Top = s {
                    *self = Self::Top
                }
            }
            ProjectionElem::Field(idx, _) => {
                let tys: IndexVec<FieldIdx, Ty<'tcx>> = match place_ty.ty.kind() {
                    TyKind::Closure(_, subst) => subst.as_closure().upvar_tys().iter().collect(),
                    TyKind::Tuple(tys) => tys.iter().collect(),
                    TyKind::Adt(def, subst) => def
                        .variant(place_ty.variant_index.unwrap_or(VariantIdx::ZERO))
                        .fields
                        .iter()
                        .map(|f| f.ty(ctx.tcx, subst))
                        .collect(),
                    _ => unreachable!(),
                };

                /* First step: create the new node if needed. */
                if let Self::TyInv = self {
                    *self = Self::Fields(
                        tys.iter_enumerated()
                            .map(|(idx, ty)| {
                                if let TyKind::Adt(def, _) = place_ty.ty.kind()
                                    && def.is_struct()
                                    && !def.non_enum_variant().fields[idx]
                                        .vis
                                        .is_accessible_from(ctx.scope, ctx.tcx)
                                {
                                    Self::Top
                                } else if is_tyinv_trivial(*ty) {
                                    Self::Top
                                } else {
                                    Self::TyInv
                                }
                            })
                            .collect(),
                    )
                } else if let Self::Top = self {
                    *self = Self::Fields(IndexVec::from_fn_n(|_| Self::Top, tys.len()))
                }

                /* Second step: recursive call. */
                let Self::Fields(flds) = self else { unreachable!() };
                flds[*idx].write(ctx, it, leaf);

                /* Third step: remove the modified node if appropriate. */
                if flds.iter().all(|t| matches!(t, Self::Top)) {
                    *self = Self::Top
                } else if let TraitResolved::NoInstance =
                    resolve_user_inv(ctx, place_ty.ty, ctx.typing_env)
                    && flds
                        .iter()
                        .zip_eq(&*tys)
                        .all(|(t, ty)| matches!(t, Self::TyInv) || is_tyinv_trivial(*ty))
                {
                    *self = Self::TyInv
                }
            }
            ProjectionElem::Downcast(_, idx) => {
                let TyKind::Adt(def, subst) = place_ty.ty.kind() else { unreachable!() };

                /* First step: create the new node if needed. */
                if let Self::TyInv = self {
                    let vs = def
                        .variants()
                        .iter()
                        .map(|v| {
                            if v.fields.iter().all(|f| is_tyinv_trivial(f.ty(ctx.tcx, subst))) {
                                Self::Top
                            } else {
                                Self::TyInv
                            }
                        })
                        .collect();
                    *self = Self::Downcasts(vs)
                } else if let Self::Top = self {
                    *self =
                        Self::Downcasts(IndexVec::from_fn_n(|_| Self::Top, def.variants().len()))
                }

                /* Second step: recursive call. */
                let Self::Downcasts(vs) = self else { unreachable!() };
                vs[*idx].write(ctx, it, leaf);

                /* Third step: remove the modified node if appropriate. */
                if vs.iter().all(|t| matches!(t, Self::Top)) {
                    *self = Self::Top
                } else if let TraitResolved::NoInstance =
                    resolve_user_inv(ctx, place_ty.ty, ctx.typing_env)
                    && vs.iter().zip_eq(def.variants()).all(|(t, v)| {
                        matches!(t, Self::TyInv)
                            || v.fields.iter().all(|f| is_tyinv_trivial(f.ty(ctx.tcx, subst)))
                    })
                {
                    *self = Self::TyInv
                }
            }
            ProjectionElem::Index(_) => {
                if let Self::Top = self {
                    return;
                }
                assert_matches!(self, Self::TyInv);

                if is_tyinv_trivial(place_ty.ty.builtin_index().unwrap()) {
                    return;
                }

                let mut c = Self::TyInv;
                c.write(ctx, it, leaf);
                if !matches!(c, Self::TyInv) {
                    *self = Self::Top
                }
            }
            _ => unimplemented!("Unimplemented place projection: {elem:?}."),
        }
    }

    fn ty_inv_projection<'tcx>(&self, projection: &[ProjectionElem<'tcx>]) -> bool {
        if let Self::TyInv = self {
            return true;
        }
        match (projection, self) {
            (_, Self::Top) | ([], _) => false,
            ([ProjectionElem::Deref, proj @ ..], Self::Deref(s)) => s.ty_inv_projection(proj),
            ([ProjectionElem::Field(idx, _), proj @ ..], Self::Fields(flds)) => {
                flds[*idx].ty_inv_projection(proj)
            }
            ([ProjectionElem::Downcast(_, idx), proj @ ..], Self::Downcasts(vs)) => {
                vs[*idx].ty_inv_projection(proj)
            }
            p => unreachable!("{p:?}"),
        }
    }

    fn to_tyinv_place_vec<'tcx>(
        &self,
        changed: &ChangedPlacesTree,
        ctx: &TranslationCtx<'tcx>,
        local: Ident,
        mut projection: Vec<ProjectionElem<'tcx>>,
        mut place_ty: PlaceTy<'tcx>,
        acc: &mut Vec<Place<'tcx>>,
    ) {
        match self {
            Self::Top => (),
            Self::TyInv => acc.push(Place { local, projection: projection.into() }),
            Self::Deref(s) => {
                let changed = match changed {
                    ChangedPlacesTree::Changed => &ChangedPlacesTree::Changed,
                    ChangedPlacesTree::Deref(box d) => d,
                    _ => unreachable!(),
                };
                projection.push(ProjectionElem::Deref);
                assert_matches!(place_ty.variant_index, None);
                place_ty.ty = place_ty.ty.builtin_deref(true).unwrap();
                s.to_tyinv_place_vec(changed, ctx, local, projection, place_ty, acc)
            }
            Self::Fields(flds) => {
                let changed: Box<dyn Iterator<Item = &Option<ChangedPlacesTree>>> = match changed {
                    ChangedPlacesTree::Changed => {
                        Box::new(repeat(&Some(ChangedPlacesTree::Changed)))
                    }
                    ChangedPlacesTree::Fields(flds) => Box::new(flds.iter()),
                    _ => unreachable!(),
                };
                for ((idx, s), changed) in flds.iter_enumerated().zip(changed) {
                    let Some(changed) = changed else { continue };
                    let ty = PlaceTy::field_ty(ctx.tcx, place_ty.ty, place_ty.variant_index, idx);
                    let mut proj = projection.clone();
                    proj.push(ProjectionElem::Field(idx, ty));
                    s.to_tyinv_place_vec(changed, ctx, local, proj, PlaceTy::from_ty(ty), acc);
                }
            }
            Self::Downcasts(vs) => {
                assert_matches!(changed, ChangedPlacesTree::Changed);
                for (idx, s) in vs.iter_enumerated() {
                    let mut proj = projection.clone();
                    proj.push(ProjectionElem::Downcast(None, idx));
                    place_ty.variant_index = Some(idx);
                    s.to_tyinv_place_vec(changed, ctx, local, proj, place_ty, acc);
                }
            }
        }
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Default)]
struct TyInvState(IndexMap<Ident, TyInvPlacesTree> /* No mapping: Top */);

impl TyInvState {
    fn ty_inv_place<'tcx>(&self, place: &Place<'tcx>) -> bool {
        let Some(t) = self.0.get(&place.local) else { return false };
        t.ty_inv_projection(&place.projection)
    }

    fn ty_inv_operand<'tcx>(&self, op: &Operand<'tcx>) -> bool {
        match op {
            Operand::Place(place) => self.ty_inv_place(place),
            Operand::ShrBorrow(op) => self.ty_inv_operand(op),
            Operand::Term(..) | Operand::InlineConst(..) => {
                /* TODO: These operands are generated (in particular) when translating constants.
                When do constants satisfy their type invariants?

                Most of the time, this is irrelevant, because in practice, constants types do not
                have a type invariant. */
                return false;
            }
        }
    }

    fn ty_inv_rvalue<'tcx>(
        &self,
        ctx: &InvariantAnalysisCtx<'_, 'tcx>,
        rv: &RValue<'tcx>,
        ty: Ty<'tcx>,
    ) -> bool {
        if is_tyinv_trivial(ctx, ctx.scope, ctx.typing_env, ty, DUMMY_SP) {
            return false;
        }

        let ty_inv_op = |op: &Operand<'tcx>| {
            is_tyinv_trivial(
                ctx,
                ctx.scope,
                ctx.typing_env,
                op.ty(ctx.tcx, &ctx.body.locals),
                DUMMY_SP,
            ) || self.ty_inv_operand(op)
        };

        match rv {
            RValue::Operand(op) => ty_inv_op(op),
            RValue::BinOp(..) | RValue::UnaryOp(..) | RValue::Cast(..) | RValue::Ptr(_) => {
                unreachable!("binary op / unary op / casts / ptr should return trivial tyinv")
            }
            RValue::Constructor(.., ops) => {
                matches!(resolve_user_inv(ctx, ty, ctx.typing_env), TraitResolved::NoInstance)
                    && ops.iter().all(ty_inv_op)
            }
            RValue::Tuple(ops) | RValue::Array(ops) => ops.iter().all(ty_inv_op),
            RValue::Repeat(op, _) => ty_inv_op(op),
        }
    }

    fn write_place<'tcx>(
        &mut self,
        ctx: &InvariantAnalysisCtx<'_, 'tcx>,
        place: &Place<'tcx>,
        ty_inv: bool,
    ) {
        let state = self.0.entry(place.local).or_insert(TyInvPlacesTree::Top);
        let mut place_ty = PlaceTy::from_ty(ctx.body.locals[&place.local].ty);
        let leaf = if ty_inv
            && !is_tyinv_trivial(
                ctx,
                ctx.scope,
                ctx.typing_env,
                place.ty(ctx.tcx, &ctx.body.locals),
                DUMMY_SP,
            ) {
            TyInvPlacesTree::TyInv
        } else {
            TyInvPlacesTree::Top
        };
        state.write(ctx, iter_projections_ty(ctx, &place.projection, &mut place_ty), leaf);
    }

    fn join(&mut self, other: &Self) {
        for (&local, o) in other.0.iter() {
            if let Entry::Occupied(mut e) = self.0.entry(local) {
                e.get_mut().join(o);
                if let TyInvPlacesTree::Top = e.get() {
                    e.swap_remove();
                }
            }
        }
    }

    fn to_tyinv_place_vec<'tcx>(
        &self,
        changed: &ChangedPlaces,
        ctx: &TranslationCtx<'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Place<'tcx>> {
        let mut acc = vec![];
        for (&local, state) in &self.0 {
            let Some(changed) = changed.0.get(&local) else { continue };
            let placety = PlaceTy::from_ty(body.locals[&local].ty);
            state.to_tyinv_place_vec(changed, ctx, local, vec![], placety, &mut acc);
        }
        acc
    }
}

fn ty_inv_analysis<'tcx>(
    ctx: &InvariantAnalysisCtx<'_, 'tcx>,
    component: &[Component<BasicBlock>],
    states: &mut IndexMap<BasicBlock, TyInvState>,
) {
    for c in component {
        match c {
            Component::Simple(v) => ty_inv_analysis_bb(ctx, *v, states),
            Component::Complex(head, rest) => loop {
                let state_ini = states[head].clone();
                ty_inv_analysis_bb(ctx, *head, states);
                ty_inv_analysis(ctx, rest, states);
                if states[head] == state_ini {
                    break;
                }
            },
        }
    }
}

fn ty_inv_analysis_bb<'tcx>(
    ctx: &InvariantAnalysisCtx<'_, 'tcx>,
    bb: BasicBlock,
    states: &mut IndexMap<BasicBlock, TyInvState>,
) {
    let Some(mut state) = states.get(&bb).cloned() else { return };

    let block = &ctx.body.blocks[&bb];
    for stmt in &block.stmts {
        match &stmt.kind {
            StatementKind::Assignment(place, rvalue) => {
                state.write_place(
                    ctx,
                    place,
                    state.ty_inv_rvalue(ctx, rvalue, place.ty(ctx.tcx, &ctx.body.locals)),
                );
            }
            StatementKind::MutBorrow(_, lhs, rhs) => {
                state.write_place(ctx, lhs, true);
                state.write_place(ctx, rhs, true);
            }
            StatementKind::Assertion { .. } => {
                /* TODO: we could decode the assertion to use user assertions such as
                `proof_assert!(inv(...))`. */
            }
            StatementKind::Call(lhs, did, ..) => {
                state.write_place(ctx, lhs, !is_open_inv_result(ctx.tcx, *did))
            }
        }
    }

    for tgt in block.terminator.targets() {
        match states.entry(tgt) {
            Entry::Occupied(mut e) => e.get_mut().join(&state),
            Entry::Vacant(e) => {
                e.insert(state.clone());
            }
        }
    }
}
