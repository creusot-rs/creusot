use indexmap::{IndexMap, IndexSet};
use rustc_middle::{
    mir::{BasicBlock, ProjectionElem, START_BLOCK, tcx::PlaceTy},
    ty::{Ty, TyCtxt},
};
use rustc_span::DUMMY_SP;

use crate::{
    backend::{
        program::node_graph,
        projections::projection_ty,
        wto::{Component, weak_topological_order},
    },
    contracts_items::get_snap_ty,
    ctx::TranslationCtx,
    translation::{
        fmir,
        pearlite::{Ident, Term},
    },
};
use petgraph::Direction;

use crate::translation::fmir::{Block, FmirVisitor, Place, RValue, Statement, Terminator};

/// fMIR transformations
///
/// This module defines a fMIR transformation which analyzes the body for
///
/// (1) types with invariants being mutated inside of a loop
/// (2) mutable borrows being mutated inside of a loop.

pub fn infer_proph_invariants<'tcx>(ctx: &TranslationCtx<'tcx>, body: &mut fmir::Body<'tcx>) {
    let graph = node_graph(body);

    let wto = weak_topological_order(&graph, START_BLOCK);
    let mut backs = IndexMap::new();
    descendants(&mut backs, &wto);

    let res = borrow_prophecy_analysis(ctx, &body, &wto);

    let snap_ty = get_snap_ty(ctx.tcx);
    let tcx = ctx.tcx;
    for (k, unchanged) in res.iter() {
        let inc = graph.neighbors_directed(*k, Direction::Incoming);
        let incoming = &inc.collect::<IndexSet<_>>() - &backs[k];

        for (ix, u) in unchanged.iter().enumerate() {
            let Some(pterm) = place_to_term(u, tcx, &body.locals) else { continue };

            let local = Ident::fresh_local(&format!("old_{}_{ix}", k.as_u32()));
            let subst = ctx.mk_args(&[u.ty(tcx, &body.locals).into()]);
            let ty = Ty::new_adt(ctx.tcx, ctx.adt_def(snap_ty), subst);

            body.locals.insert(local, fmir::LocalDecl {
                span: DUMMY_SP,
                ty,
                temp: true,
                arg: false,
            });

            for p in &incoming {
                let mut prev_block = body.blocks.get_mut(p).unwrap();
                if let Terminator::Switch(_, branches) = &mut prev_block.terminator {
                    let new_block = BasicBlock::from(body.fresh);
                    body.fresh += 1;
                    for tgt in branches.targets_mut() {
                        if *tgt == *k {
                            *tgt = new_block;
                        }
                    }
                    body.blocks.insert(new_block, Block {
                        invariants: vec![],
                        variant: None,
                        stmts: vec![],
                        terminator: Terminator::Goto(*k),
                    });
                    prev_block = body.blocks.get_mut(&new_block).unwrap();
                }
                if let Terminator::Goto(t) = prev_block.terminator
                    && t == *k
                {
                } else {
                    panic!()
                }
                prev_block.stmts.push(Statement::Assignment(
                    Place { local, projections: Box::new([]) },
                    RValue::Snapshot(pterm.clone().coerce(ty)),
                    DUMMY_SP,
                ));
            }

            let old = Term::var(local, ty);
            let blk = body.blocks.get_mut(k).unwrap();

            blk.invariants.insert(0, fmir::Invariant {
                body: old.coerce(u.ty(tcx, &body.locals)).fin().eq(tcx, pterm.fin()),
                expl: "expl:mut invariant".to_string(),
            });
        }
    }
}

fn place_to_term<'tcx>(
    p: &Place<'tcx>,
    tcx: TyCtxt<'tcx>,
    locals: &fmir::LocalDecls<'tcx>,
) -> Option<Term<'tcx>> {
    let mut t = Term::var(p.local, locals[&p.local].ty);
    let mut pty = PlaceTy::from_ty(locals[&p.local].ty);

    for proj in &p.projections {
        let res_ty = projection_ty(pty, tcx, proj);
        match proj {
            ProjectionElem::Deref => {
                if pty.ty.is_mutable_ptr() {
                    t = t.cur();
                }
            }
            ProjectionElem::Field(ix, _) => t = t.proj(*ix, res_ty.ty),
            ProjectionElem::Index(_) => return None,
            ProjectionElem::ConstantIndex { .. } => return None,
            ProjectionElem::Subslice { .. } => return None,
            ProjectionElem::Downcast(_, _) => return None,
            ProjectionElem::OpaqueCast(_) => return None,
            ProjectionElem::Subtype(_) => return None,
        }

        pty = res_ty;
    }

    Some(t)
}

fn descendants(
    e: &mut IndexMap<BasicBlock, IndexSet<BasicBlock>>,
    comps: &[Component<BasicBlock>],
) {
    for comp in comps {
        match comp {
            Component::Vertex(_) => (),
            Component::Component(l, members) => {
                descendants(e, members);
                for mem in members {
                    match mem {
                        Component::Vertex(b) => {
                            e.entry(*l).or_default().insert(*b);
                        }
                        Component::Component(b, _) => {
                            let s = e[b].clone();
                            e.entry(*l).or_default().union(&s);
                        }
                    }
                }
            }
        }
    }
}

fn borrow_prophecy_analysis<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &fmir::Body<'tcx>,
    c: &[Component<BasicBlock>],
) -> IndexMap<BasicBlock, IndexSet<Place<'tcx>>> {
    let mut unchanged_prophs = Default::default();
    let mut state = BorrowProph::initialize(ctx, &body.locals, &mut unchanged_prophs);

    for comp in c {
        borrow_prophecy_analysis_inner(&mut state, ctx, body, comp);
    }

    unchanged_prophs
}

fn borrow_prophecy_analysis_inner<'a, 'tcx>(
    state_parent: &mut BorrowProph<'a, 'tcx>,
    ctx: &'a TranslationCtx<'tcx>,
    body: &'a fmir::Body<'tcx>,
    c: &Component<BasicBlock>,
) {
    match c {
        Component::Vertex(b) => state_parent.visit_block(&body.blocks[b]),
        Component::Component(h, l) => {
            let mut state =
                BorrowProph::initialize(ctx, &body.locals, state_parent.unchanged_prophs);
            state.visit_block(&body.blocks[h]);

            for b in l {
                borrow_prophecy_analysis_inner(&mut state, ctx, body, b)
            }

            let mut unchanged_prophs_here = IndexSet::new();
            'active_borrows: for b in &state.active_borrows {
                let mut p = b.clone();
                loop {
                    if state.overwritten_values.contains(&p) {
                        continue 'active_borrows;
                    }

                    p.projections = if let Some((_, tl)) = p.projections.split_last() {
                        tl.iter().cloned().collect()
                    } else {
                        break;
                    }
                }

                unchanged_prophs_here.insert(b.clone());
            }

            state_parent.active_borrows.extend(state.active_borrows);
            state_parent.overwritten_values.extend(state.overwritten_values);

            state_parent.unchanged_prophs.insert(*h, unchanged_prophs_here);
        }
    }
}

struct BorrowProph<'a, 'tcx> {
    active_borrows: IndexSet<Place<'tcx>>,
    overwritten_values: IndexSet<Place<'tcx>>,
    locals: &'a fmir::LocalDecls<'tcx>,
    unchanged_prophs: &'a mut IndexMap<BasicBlock, IndexSet<Place<'tcx>>>,
    tcx: TyCtxt<'tcx>,
}

impl<'a, 'tcx> BorrowProph<'a, 'tcx> {
    fn record_write_to(&mut self, pl: &Place<'tcx>) {
        self.overwritten_values.insert(pl.clone());

        let mut bty = PlaceTy::from_ty(self.locals[&pl.local].ty);
        let mut proj = vec![];
        for pr in &pl.projections {
            let b = Place { projections: proj.clone().into(), ..*pl };
            if matches!(pr, ProjectionElem::Deref) && bty.ty.is_ref() && bty.ty.is_mutable_ptr() {
                self.active_borrows.insert(b.clone());
            }
            proj.push(*pr);
            bty = projection_ty(bty, self.tcx, pr);
        }
    }
}

impl<'a, 'tcx> FmirVisitor<'tcx> for BorrowProph<'a, 'tcx> {
    fn visit_stmt(&mut self, stmt: &fmir::Statement<'tcx>) {
        match stmt {
            fmir::Statement::Assignment(l, r, _) => {
                self.record_write_to(l);

                if let RValue::Borrow(_, r, _) = r {
                    self.record_write_to(r);
                }
            }
            fmir::Statement::Call(r, _, _, _, _) => {
                self.record_write_to(r);
            }
            _ => (),
        }
    }
}

impl<'a, 'tcx> BorrowProph<'a, 'tcx> {
    fn initialize(
        ctx: &'a TranslationCtx<'tcx>,
        locals: &'a fmir::LocalDecls<'tcx>,
        unchanged_prophs: &'a mut IndexMap<BasicBlock, IndexSet<Place<'tcx>>>,
    ) -> Self {
        {
            Self {
                tcx: ctx.tcx,
                locals,
                active_borrows: Default::default(),
                overwritten_values: Default::default(),
                unchanged_prophs: unchanged_prophs,
            }
        }
    }
}
