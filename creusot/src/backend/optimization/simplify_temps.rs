use rustc_middle::{
    mir::{BasicBlock, START_BLOCK},
    ty::TyKind,
};

use crate::{
    backend::{
        optimization::remove_dead_locals::PurityVisitor,
        program::node_graph,
        wto::{Component, weak_topological_order},
    },
    contracts_items::Intrinsic,
    ctx::TranslationCtx,
    translation::{
        fmir::{
            Body, FmirVisitor, FmirVisitorMut, LocalDecls, Operand, Place, ProjectionElem, RValue,
            Statement, StatementKind, Terminator, super_visit_mut_operand, super_visit_mut_rvalue,
            super_visit_mut_stmt, super_visit_operand, super_visit_place, super_visit_rvalue,
            super_visit_terminator,
        },
        pearlite::{
            Ident, PIdent, Term, TermKind,
            visit::{TermVisitor, super_visit_term},
        },
    },
};
use std::collections::{HashMap, hash_map::Entry};

/// Simplify the given fMIR body
/// - Propagate temporaries that are only read and written once.
pub(crate) fn simplify_temporaries<'tcx>(ctx: &TranslationCtx<'tcx>, body: &mut Body<'tcx>) {
    let reads = gather_reads(body);
    let ini_state: State<'tcx> = State(
        reads
            .iter()
            .filter_map(|(&l, &r)| {
                (body.locals[&l].temp && r == Reads::One).then_some((l, LocalState::Top))
            })
            .collect(),
    );
    let mut states = HashMap::from([(START_BLOCK, ini_state)]);
    analyze_component(
        ctx,
        body,
        &weak_topological_order(&node_graph(body), START_BLOCK),
        &mut states,
    );

    for (bb, block) in &mut body.blocks {
        for s in block.stmts.iter_mut() {
            if let StatementKind::Assignment(ref lhs, RValue::Operand(Operand::Term(_, ref mut b))) =
                s.kind
                && let Some(Reads::Zero) = reads.get(&lhs.local)
                && let TyKind::Adt(def, _) = body.locals[&lhs.local].ty.kind()
                && Intrinsic::Snapshot.is(ctx, def.did())
            {
                // This snapshot is never read. Mark it so that we will keep it in the dead temps
                // optimization.
                *b = true
            }
        }

        if let Some(mut state) = states.remove(bb) {
            BlockPropagator { ctx, locals: &body.locals, state: &mut state, readonly: false }
                .visit_mut_block(block);
        }
    }
}

/// A visitor that collect informations about reads of local temporaries.
#[derive(Debug)]
struct LocalReads(HashMap<Ident, Reads>);

/// Used to record reads of a local temporaries
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Reads {
    Zero,
    One,              // One substitutable read
    NotSubstitutable, // Several reads or one non-substitutable read
}

impl Reads {
    fn inc(&mut self) {
        *self = match self {
            Reads::Zero => Reads::One,
            Reads::One => Reads::NotSubstitutable,
            Reads::NotSubstitutable => Reads::NotSubstitutable,
        }
    }
}

/// Analyzes `body` to gather informations about reads of local temporaries.
fn gather_reads(body: &Body) -> HashMap<Ident, Reads> {
    // Only consider reads of local temporaries
    let reads = body
        .locals
        .iter()
        .skip(1) // Skip return local
        .map(|(&l, _)| (l, Reads::Zero))
        .collect();
    let mut usage = LocalReads(reads);
    usage.visit_body(body);
    usage.0
}

impl<'tcx> FmirVisitor<'tcx> for LocalReads {
    fn visit_terminator(&mut self, t: &Terminator<'tcx>) {
        super_visit_terminator(self, t);
        // Technically, we need to record the read of the return local, but it is not
        // in `self.0`` anyway
    }

    fn visit_rvalue(&mut self, r: &RValue<'tcx>) {
        super_visit_rvalue(self, r);
        if let RValue::MutBorrow(_, p) | RValue::Ptr(p) = r
            && let Some(r) = self.0.get_mut(&p.local)
        {
            *r = Reads::NotSubstitutable
        }
    }

    fn visit_operand(&mut self, op: &Operand<'tcx>) {
        if let Operand::Place(p) = op
            && let Some(r) = self.0.get_mut(&p.local)
        {
            if p.projection.len() == 0 { r.inc() } else { *r = Reads::NotSubstitutable }
        }
        super_visit_operand(self, op)
    }

    fn visit_place(&mut self, p: &Place<'tcx>) {
        super_visit_place(self, p);
        for e in &p.projection {
            if let ProjectionElem::Index(PIdent(l)) = e
                && let Some(r) = self.0.get_mut(l)
            {
                *r = Reads::NotSubstitutable
            }
        }
    }

    fn visit_term(&mut self, term: &Term<'tcx>) {
        TermVisitor::visit_term(self, term)
    }
}

impl<'tcx> TermVisitor<'tcx> for LocalReads {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        super_visit_term(term, self);
        if let TermKind::Var(PIdent(v)) = term.kind
            && let Some(r) = self.0.get_mut(&v)
        {
            *r = Reads::NotSubstitutable
        }
    }
}

/// Abstract state for the main analysis: state for one local temp
#[derive(Clone, Debug)]
enum LocalState<'tcx> {
    Top,
    Op(Operand<'tcx>, *const Operand<'tcx>),
}

impl<'tcx> PartialEq for LocalState<'tcx> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Top, Self::Top) => true,
            (Self::Op(_, p1), Self::Op(_, p2)) => p1 == p2,
            _ => false,
        }
    }
}

impl<'tcx> LocalState<'tcx> {
    fn join(&mut self, other: &LocalState<'tcx>) {
        match (&mut *self, other) {
            (_, Self::Top) => *self = Self::Top,
            (Self::Op(_, p1), Self::Op(_, p2)) if p1 != p2 => *self = Self::Top,
            _ => (),
        }
    }
}

/// Abstract state for the main analysis: global state
#[derive(Clone, PartialEq, Debug)]
struct State<'tcx>(HashMap<Ident, LocalState<'tcx>>);

impl<'tcx> State<'tcx> {
    fn join(&mut self, other: &State<'tcx>) {
        for (l, st) in other.0.iter() {
            self.0.get_mut(l).unwrap().join(st)
        }
    }
}

/// Compute the fixed point of the abstract state for one WTO component
fn analyze_component<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &mut Body<'tcx>,
    component: &[Component<BasicBlock>],
    states: &mut HashMap<BasicBlock, State<'tcx>>,
) {
    for c in component {
        match c {
            Component::Simple(v) => propagate_temporaries_bb(ctx, body, *v, states, true),
            Component::Complex(head, rest) => {
                loop {
                    let state_ini = states[head].clone();
                    propagate_temporaries_bb(ctx, body, *head, states, true);
                    analyze_component(ctx, body, rest, states);
                    if states[head] == state_ini {
                        // We expect the iteration to converge in 2 steps in most of the cases
                        break;
                    }
                }
            }
        }
    }
}

/// Propagate the abstract state through one BB.
/// If [readonly == false], also replaces RHS of assignments using the values
/// found in the abstract state
fn propagate_temporaries_bb<'tcx>(
    ctx: &TranslationCtx<'tcx>,
    body: &mut Body<'tcx>,
    bb: BasicBlock,
    states: &mut HashMap<BasicBlock, State<'tcx>>,
    readonly: bool,
) {
    let Some(mut state) = states.get(&bb).cloned() else { return };
    let block = &mut body.blocks[&bb];
    BlockPropagator { ctx, locals: &body.locals, state: &mut state, readonly }
        .visit_mut_block(block);
    for tgt in block.terminator.targets() {
        match states.entry(tgt) {
            Entry::Occupied(e) => e.into_mut().join(&state),
            Entry::Vacant(e) => {
                e.insert(state.clone());
            }
        }
    }
}

/// The visitor that does all the had work of `propagate_temporaries_bb`.
struct BlockPropagator<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    locals: &'a LocalDecls<'tcx>,
    state: &'a mut State<'tcx>,
    readonly: bool,
}

impl<'tcx> FmirVisitorMut<'tcx> for BlockPropagator<'_, 'tcx> {
    fn visit_mut_operand(&mut self, op: &mut Operand<'tcx>) {
        super_visit_mut_operand(self, op);
        if self.readonly {
            return;
        }
        while let Operand::Place(p) = op
            && p.projection.len() == 0
            && let Some(LocalState::Op(op_new, _)) = self.state.0.get(&p.local)
        {
            *op = op_new.clone();
        }
    }

    fn visit_mut_stmt(&mut self, stmt: &mut Statement<'tcx>) {
        super_visit_mut_stmt(self, stmt);
        let lhs = match &mut stmt.kind {
            StatementKind::Assignment(lhs, RValue::Operand(rhs)) if lhs.projection.len() == 0 => {
                if self.state.0.contains_key(&lhs.local) {
                    let (locals, ctx) = (self.locals, self.ctx);
                    let mut pure = PurityVisitor { locals, ctx, span: stmt.span, pure: true };
                    pure.visit_place(lhs);
                    pure.visit_operand(rhs);
                    *self.state.0.get_mut(&lhs.local).unwrap() = if !pure.pure {
                        // This assignment is not pure. Thus, it will stay after remove_dead_locals.
                        // It is therefore pointless to propagate it.
                        LocalState::Top
                    } else {
                        LocalState::Op(rhs.clone(), rhs)
                    };
                }
                lhs
            }
            StatementKind::Assignment(lhs, _) | StatementKind::Call(lhs, ..) => {
                if let Some(r) = self.state.0.get_mut(&lhs.local) {
                    *r = LocalState::Top
                }
                lhs
            }
            StatementKind::Assertion { .. } => return,
        };

        /* Erase mappings which are invalidated by that write */
        self.erase_dependant(lhs);
    }

    fn visit_mut_rvalue(&mut self, rval: &mut RValue<'tcx>) {
        super_visit_mut_rvalue(self, rval);
        if let RValue::MutBorrow(_, pl) = rval {
            self.erase_dependant(pl);
        }
    }
}

impl<'tcx> BlockPropagator<'_, 'tcx> {
    fn erase_dependant(&mut self, pl: &Place<'tcx>) {
        for (_, st) in self.state.0.iter_mut() {
            if let LocalState::Op(op, _) = st {
                let mut op = op;
                while let Operand::ShrBorrow(box o) = op {
                    op = o
                }
                match op {
                    // TODO: use a less coarse-grain criterion to determine that p
                    // and pl do not overlap.
                    Operand::Place(p) if p.local == pl.local => {}
                    Operand::Term(t, _) if t.free_vars().contains(&pl.local) => {}
                    _ => continue
                }
            }
            *st = LocalState::Top
        }
    }
}
