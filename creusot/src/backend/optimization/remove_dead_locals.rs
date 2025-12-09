use crate::{
    backend::projections::iter_projections_ty,
    ctx::TranslationCtx,
    translation::{
        fmir::{
            Body, FmirVisitor, LocalDecls, Operand, Place, ProjectionElem, RValue, Statement,
            StatementKind, Terminator, super_visit_operand, super_visit_place, super_visit_rvalue,
            super_visit_stmt, super_visit_terminator,
        },
        pearlite::{
            Ident, PIdent, Term, TermKind,
            visit::{TermVisitor, super_visit_term},
        },
    },
};
use rustc_middle::{
    mir::{BinOp, PlaceTy, UnOp},
    ty::TyKind,
};
use rustc_span::Span;
use std::collections::HashSet;

pub(crate) fn remove_dead_locals<'tcx>(ctx: &TranslationCtx<'tcx>, body: &mut Body<'tcx>) {
    let live = gather_live(ctx, body);
    for (_, block) in &mut body.blocks {
        for s in std::mem::take(&mut block.stmts) {
            if let StatementKind::Assignment(l, _) = &s.kind
                && !live.contains(&l.local)
            {
                continue;
            }
            block.stmts.push(s)
        }
    }
    body.locals.retain(|l, _| live.contains(l));
}

struct LocalReads<'a, 'tcx> {
    ctx: &'a TranslationCtx<'tcx>,
    locals: &'a LocalDecls<'tcx>,
    return_local: Ident,
    live: HashSet<Ident>,
}

fn gather_live<'tcx>(ctx: &TranslationCtx<'tcx>, body: &Body<'tcx>) -> HashSet<Ident> {
    let return_local = *body.locals.get_index(0).unwrap().0;
    let mut usage = LocalReads { ctx, locals: &body.locals, return_local, live: HashSet::new() };
    usage.visit_body(body);
    usage.live
}

impl<'tcx> FmirVisitor<'tcx> for LocalReads<'_, 'tcx> {
    fn visit_terminator(&mut self, t: &Terminator<'tcx>) {
        super_visit_terminator(self, t);
        if let Terminator::Return = t {
            self.live.insert(self.return_local);
        }
    }

    fn visit_stmt(&mut self, s: &Statement<'tcx>) {
        super_visit_stmt(self, s);
        let l = match &s.kind {
            StatementKind::Assignment(l, r) => {
                let mut pure =
                    PurityVisitor { locals: self.locals, ctx: self.ctx, span: s.span, pure: true };
                pure.visit_place(l);
                pure.visit_rvalue(r);
                if pure.pure && !matches!(r, RValue::Operand(Operand::Term(_, true))) {
                    return;
                }
                l
            }
            StatementKind::Call(l, _, _, _, _) => l,
            _ => return,
        };
        // This assignment is not pure, so the local must stay
        self.live.insert(l.local);
    }

    fn visit_rvalue(&mut self, r: &RValue<'tcx>) {
        super_visit_rvalue(self, r);
        if let RValue::Borrow(_, p) | RValue::Ptr(p) = r {
            self.live.insert(p.local);
        }
    }

    fn visit_operand(&mut self, op: &Operand<'tcx>) {
        super_visit_operand(self, op);
        if let Operand::Place(p) = op {
            self.live.insert(p.local);
        }
    }

    fn visit_place(&mut self, p: &Place<'tcx>) {
        super_visit_place(self, p);
        p.projection.iter().for_each(|p| {
            if let ProjectionElem::Index(PIdent(l)) = p {
                self.live.insert(*l);
            }
        })
    }

    fn visit_term(&mut self, term: &Term<'tcx>) {
        TermVisitor::visit_term(self, term)
    }
}

impl<'tcx> TermVisitor<'tcx> for LocalReads<'_, 'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        super_visit_term(term, self);
        if let TermKind::Var(PIdent(v)) = term.kind {
            self.live.insert(v);
        }
    }
}

/// Visitor for rvalues that determines if the RValue generales a verification condition.
/// Note that, in some cases, the VC that will be generated is always guaranteed to hold (ex:
/// `ProjectionElem::Field``), but we still choose to consider this as non-pure, as a matter of
/// coherence. If on day we change the translation of these construct to not emit a VC, then we
/// can consider them pure here.
pub(super) struct PurityVisitor<'a, 'tcx> {
    pub locals: &'a LocalDecls<'tcx>,
    pub ctx: &'a TranslationCtx<'tcx>,
    pub span: Span,
    pub pure: bool,
}

impl<'tcx> FmirVisitor<'tcx> for PurityVisitor<'_, 'tcx> {
    fn visit_place(&mut self, pl: &Place<'tcx>) {
        let mut place_ty = PlaceTy::from_ty(self.locals[&pl.local].ty);
        for (elem, place_ty) in iter_projections_ty(self.ctx, &pl.projection, &mut place_ty) {
            match elem {
                ProjectionElem::Deref => (),
                ProjectionElem::Field(..) => match place_ty.ty.kind() {
                    TyKind::Adt(def, _) if def.is_enum() || def.is_union() => self.pure = false,
                    _ => (),
                },
                ProjectionElem::Index(_) => self.pure = false,
                ProjectionElem::Downcast(..) => (), // Handled in `Field` case
                // UNSUPPORTED
                ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. }
                | ProjectionElem::OpaqueCast(_)
                | ProjectionElem::UnwrapUnsafeBinder(_) => {
                    self.ctx.dcx().span_bug(self.span, format!("Unsupported projection {elem:?}"))
                }
            }
        }
    }

    fn visit_operand(&mut self, op: &Operand<'tcx>) {
        super_visit_operand(self, op);
        match op {
            Operand::Place(_) | Operand::Term(..) => {}
            _ => self.pure = false,
        }
    }

    fn visit_rvalue(&mut self, rv: &RValue<'tcx>) {
        super_visit_rvalue(self, rv);
        match rv {
            RValue::Operand(_)
            | RValue::BinOp(
                BinOp::AddWithOverflow
                | BinOp::SubWithOverflow
                | BinOp::MulWithOverflow
                | BinOp::BitAnd
                | BinOp::BitOr
                | BinOp::BitXor
                | BinOp::Cmp
                | BinOp::Eq
                | BinOp::Ne
                | BinOp::Lt
                | BinOp::Le
                | BinOp::Gt
                | BinOp::Ge,
                _,
                _,
            )
            | RValue::UnaryOp(UnOp::Not | UnOp::PtrMetadata, _)
            | RValue::Constructor(_, _, _)
            | RValue::Tuple(_)
            | RValue::Array(_)
            | RValue::Repeat(_, _)
            | RValue::Borrow(_, _)
            | RValue::Ptr(_) => {}
            _ => self.pure = false,
        }
    }
}
