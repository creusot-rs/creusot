use indexmap::{IndexMap, IndexSet};
use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{tcx::PlaceTy, BasicBlock, ProjectionElem, START_BLOCK},
    ty::{Ty, TyCtxt},
};
use rustc_span::{Symbol, DUMMY_SP};

use crate::{
    backend::{
        place::projection_ty,
        program::node_graph,
        wto::{weak_topological_order, Component},
    },
    ctx::TranslationCtx,
    fmir::BorrowKind,
    pearlite::{mk_projection, BinOp, Term},
    translation::fmir,
};
use petgraph::Direction;

use crate::translation::fmir::{FmirVisitor, Place, RValue, Statement};

/// fMIR transformations
///
/// This module defines a fMIR transformation which analyzes the body for
///
/// (1) types with invariants being mutated inside of a loop
/// (2) mutable borrows being mutated inside of a loop.

pub fn infer_proph_invariants<'tcx>(
    ctx: &mut TranslationCtx<'tcx>,
    self_id: DefId,
    body: &mut fmir::Body<'tcx>,
) {
    let graph = node_graph(body);

    let wto = weak_topological_order(&graph, START_BLOCK);
    let mut backs = IndexMap::new();
    backedges(&mut backs, &wto);

    let res = borrow_prophecy_analysis(ctx, self_id, &body, &wto);

    let Some(snap_ty) = ctx.get_diagnostic_item(Symbol::intern("snapshot_ty")) else { return };
    let Some(snap_new) = ctx.get_diagnostic_item(Symbol::intern("snapshot_new")) else { return };
    let Some(snap_deref) = ctx.get_diagnostic_item(Symbol::intern("snapshot_deref")) else {
        return;
    };
    let tcx = ctx.tcx;
    for (k, unchanged) in res.iter() {
        let inc = graph.neighbors_directed(*k, Direction::Incoming);
        let incoming = &inc.collect::<IndexSet<_>>() - &backs[k];

        for (ix, u) in unchanged.iter().enumerate() {
            let local = Symbol::intern(&format!("old_{}_{ix}", k.as_u32()));
            let subst = ctx.mk_args(&[u.ty(tcx, &body.locals).into()]);
            let ty = Ty::new_adt(ctx.tcx, ctx.adt_def(snap_ty), subst);

            body.locals
                .insert(local, fmir::LocalDecl { span: DUMMY_SP, ty, temp: true, arg: false });

            let Some(pterm) = place_to_term(u, tcx, &body.locals) else { break };
            for p in &incoming {
                let block = body.blocks.get_mut(p).unwrap();
                block.stmts.push(Statement::Assignment(
                    Place { local, projection: Vec::new() },
                    RValue::Ghost(Term::call(tcx, snap_new, subst, vec![pterm.clone()])),
                    DUMMY_SP,
                ));
            }

            let old = Term::var(local, ty);
            let blk = body.blocks.get_mut(k).unwrap();

            let snap_old = Term::call(ctx.tcx, snap_deref, subst, vec![old]);
            let mut snap_old = ctx
                .try_normalize_erasing_regions(ctx.param_env(self_id), snap_old.clone())
                .unwrap_or(snap_old);
            snap_old.ty = snap_old.ty.builtin_deref(true).unwrap();
            blk.invariants.push(snap_old.fin().bin_op(tcx, BinOp::Eq, pterm.fin()));
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

    for proj in &p.projection {
        let res_ty = projection_ty(pty, tcx, *proj);
        match proj {
            ProjectionElem::Deref => {
                if pty.ty.is_mutable_ptr() {
                    t = t.cur();
                }
            }
            ProjectionElem::Field(ix, _) => {
                t = Term { kind: mk_projection(t, *ix), ty: res_ty.ty, span: DUMMY_SP };
            }
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

fn backedges(e: &mut IndexMap<BasicBlock, IndexSet<BasicBlock>>, comps: &[Component<BasicBlock>]) {
    for comp in comps {
        match comp {
            Component::Vertex(_) => (),
            Component::Component(l, members) => {
                e.entry(*l).or_default().extend(ids(members));
                backedges(e, members);
            }
        }
    }
}

fn ids(comps: &[Component<BasicBlock>]) -> Vec<BasicBlock> {
    let mut blks = Vec::new();
    for c in comps {
        match c {
            Component::Vertex(b) => blks.push(*b),
            Component::Component(l, members) => {
                blks.push(*l);
                blks.extend(ids(&members))
            }
        }
    }
    blks
}

fn borrow_prophecy_analysis<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    self_id: DefId,
    body: &fmir::Body<'tcx>,
    c: &[Component<BasicBlock>],
) -> IndexMap<BasicBlock, IndexSet<Place<'tcx>>> {
    let mut state = BorrowProph::initialize(ctx, self_id, &body.locals);

    for comp in c {
        borrow_prophecy_analysis_inner(&mut state, ctx, self_id, body, comp);
    }
    state.unchanged_prophs
}

fn borrow_prophecy_analysis_inner<'a, 'tcx>(
    vals: &mut BorrowProph<'a, 'tcx>,
    ctx: &'a TranslationCtx<'tcx>,
    self_id: DefId,
    body: &'a fmir::Body<'tcx>,
    c: &Component<BasicBlock>,
) {
    match c {
        Component::Vertex(b) => vals.visit_block(&body.blocks[b]),
        Component::Component(h, l) => {
            let mut state = BorrowProph::initialize(ctx, self_id, &body.locals);
            state.visit_block(&body.blocks[h]);

            for b in l {
                borrow_prophecy_analysis_inner(&mut state, ctx, self_id, body, b)
            }

            vals.unchanged_prophs.insert(*h, &state.active_borrows - &state.overwritten_values);
        }
    }
}

struct BorrowProph<'a, 'tcx> {
    active_borrows: IndexSet<Place<'tcx>>,
    overwritten_values: IndexSet<Place<'tcx>>,
    locals: &'a fmir::LocalDecls<'tcx>,
    unchanged_prophs: IndexMap<BasicBlock, IndexSet<Place<'tcx>>>,
    tcx: TyCtxt<'tcx>, // values: MutatedVals<'a, 'tcx>,
}

impl<'a, 'tcx> FmirVisitor<'tcx> for BorrowProph<'a, 'tcx> {
    fn visit_stmt(&mut self, stmt: &fmir::Statement<'tcx>) {
        match stmt {
            fmir::Statement::Assignment(l, r, _) => {
                self.overwritten_values.insert(l.clone());
                for_place_tys(self.tcx, l, self.locals, |projs, ty| {
                    if ty.is_mutable_ptr() && ty.is_ref() {
                        let mut pl = l.clone();
                        pl.projection = projs.to_vec();
                        self.active_borrows.insert(pl);
                        false
                    } else {
                        true
                    }
                });

                if let RValue::Borrow(BorrowKind::Mut, r) = &r {
                    for_place_tys(self.tcx, r, self.locals, |projs, ty| {
                        if ty.is_mutable_ptr() && ty.is_ref() {
                            let mut pl = r.clone();
                            pl.projection = projs.to_vec();
                            self.active_borrows.insert(pl);
                            false
                        } else {
                            true
                        }
                    })
                }
            }
            fmir::Statement::Call(r, _, _, _, _) => {
                self.overwritten_values.insert(r.clone());
            }
            _ => (),
        }
    }
}

impl<'a, 'tcx> BorrowProph<'a, 'tcx> {
    fn initialize(
        ctx: &'a TranslationCtx<'tcx>,
        _: DefId,
        locals: &'a fmir::LocalDecls<'tcx>,
    ) -> Self {
        {
            Self {
                tcx: ctx.tcx,
                locals,
                active_borrows: Default::default(),
                overwritten_values: Default::default(),
                unchanged_prophs: Default::default(),
                // values: MutatedVals::initialize(ctx, self_id, locals),
            }
        }
    }
}

fn for_place_tys<'tcx, F: FnMut(&[ProjectionElem<Symbol, Ty<'tcx>>], Ty<'tcx>) -> bool>(
    tcx: TyCtxt<'tcx>,
    place: &Place<'tcx>,
    locals: &fmir::LocalDecls<'tcx>,
    mut f: F,
) {
    let mut pty = PlaceTy::from_ty(locals[&place.local].ty);
    let mut ix = 0;

    if !f(&place.projection[..ix], pty.ty) {
        return;
    }

    for p in &place.projection {
        pty = projection_ty(pty, tcx, *p);
        ix += 1;

        if !f(&place.projection[..ix], pty.ty) {
            break;
        }
    }
}
