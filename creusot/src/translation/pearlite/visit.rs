use rustc_middle::mir::ProjectionElem;

use crate::translation::pearlite::{Pattern, PatternKind, Projections, Term, TermKind};

pub trait TermVisitor<'tcx>: Sized {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        super_visit_term(term, self);
    }

    #[allow(dead_code)] // TODO: not checking patterns causes `opacity.rs` to be overly permissive
    fn visit_pattern(&mut self, pat: &Pattern<'tcx>) {
        super_visit_pattern(pat, self);
    }
}

pub fn super_visit_term<'tcx, V: TermVisitor<'tcx>>(term: &Term<'tcx>, visitor: &mut V) {
    match &term.kind {
        TermKind::Var(_) | TermKind::Lit(_) | TermKind::Capture(_) => (),
        TermKind::SeqLiteral(fields) => fields.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Cast { arg } => visitor.visit_term(arg),
        TermKind::Coerce { arg } => visitor.visit_term(arg),
        TermKind::Item(_, _) | TermKind::Const(_) => {}
        TermKind::Binary { op: _, lhs, rhs } => {
            visitor.visit_term(lhs);
            visitor.visit_term(rhs);
        }
        TermKind::Unary { op: _, arg } => visitor.visit_term(arg),
        TermKind::Quant { body, trigger, .. } => {
            trigger.iter().flat_map(|x| &x.0).for_each(|x| visitor.visit_term(x));
            visitor.visit_term(body)
        }
        TermKind::Call { id: _, subst: _, args } => args.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Constructor { variant: _, fields } => {
            fields.iter().for_each(|a| visitor.visit_term(a))
        }
        TermKind::Tuple { fields } => fields.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Cur { term } => visitor.visit_term(term),
        TermKind::Fin { term } => visitor.visit_term(term),
        TermKind::Impl { lhs, rhs } => {
            visitor.visit_term(lhs);
            visitor.visit_term(rhs)
        }
        TermKind::Match { scrutinee, arms } => {
            visitor.visit_term(scrutinee);
            arms.iter().for_each(|(_pattern, arm)| {
                // visitor.visit_pattern(pattern); // Issue #1672
                visitor.visit_term(arm)
            })
        }
        TermKind::Let { pattern: _, arg, body } => {
            // visitor.visit_pattern(pattern); // Issue #1672
            visitor.visit_term(arg);
            visitor.visit_term(body)
        }
        TermKind::Projection { lhs, idx: _ } => visitor.visit_term(lhs),
        TermKind::Old { term } => visitor.visit_term(term),
        TermKind::Closure { body, .. } => visitor.visit_term(body),
        TermKind::Reborrow { inner, projections } => {
            visitor.visit_term(inner);
            visit_projections(projections, |term| visitor.visit_term(term))
        }
        TermKind::Assert { cond } => visitor.visit_term(cond),
        TermKind::Precondition { params, .. } => params.iter().for_each(|a| visitor.visit_term(a)),
        TermKind::Postcondition { params, .. } => params.iter().for_each(|a| visitor.visit_term(a)),
    }
}

pub fn super_visit_pattern<'tcx, V: TermVisitor<'tcx>>(pattern: &Pattern<'tcx>, visitor: &mut V) {
    match &pattern.kind {
        PatternKind::Constructor(_, patterns) => {
            patterns.iter().for_each(|(_, p)| visitor.visit_pattern(p))
        }
        PatternKind::Deref(pattern) => visitor.visit_pattern(pattern),
        PatternKind::Tuple(patterns) => patterns.iter().for_each(|p| visitor.visit_pattern(p)),
        PatternKind::Wildcard | PatternKind::Binder(_) | PatternKind::Bool(_) => (),
        PatternKind::Or(patterns) => patterns.iter().for_each(|p| visitor.visit_pattern(p)),
    }
}

pub trait TermVisitorMut<'tcx>: Sized {
    fn visit_mut_term(&mut self, term: &mut Term<'tcx>) {
        super_visit_mut_term(term, self);
    }
}

pub(crate) fn super_visit_mut_term<'tcx, V: TermVisitorMut<'tcx>>(
    term: &mut Term<'tcx>,
    visitor: &mut V,
) {
    match &mut term.kind {
        TermKind::Var(_) | TermKind::Lit(_) | TermKind::Capture(_) => (),
        TermKind::SeqLiteral(fields) => fields.iter_mut().for_each(|a| visitor.visit_mut_term(a)),
        TermKind::Cast { arg } => visitor.visit_mut_term(&mut *arg),
        TermKind::Coerce { arg } => visitor.visit_mut_term(arg),
        TermKind::Item(..) | TermKind::Const(_) => {}
        TermKind::Binary { lhs, rhs, .. } => {
            visitor.visit_mut_term(&mut *lhs);
            visitor.visit_mut_term(&mut *rhs);
        }
        TermKind::Unary { arg, .. } => visitor.visit_mut_term(&mut *arg),
        TermKind::Quant { body, trigger, .. } => {
            trigger.iter_mut().flat_map(|x| &mut x.0).for_each(|x| visitor.visit_mut_term(x));
            visitor.visit_mut_term(&mut *body)
        }
        TermKind::Call { args, .. } => {
            args.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Constructor { fields, .. } => {
            fields.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Tuple { fields } => {
            fields.iter_mut().for_each(|a| visitor.visit_mut_term(&mut *a))
        }
        TermKind::Cur { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Fin { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Impl { lhs, rhs } => {
            visitor.visit_mut_term(&mut *lhs);
            visitor.visit_mut_term(&mut *rhs)
        }
        TermKind::Match { scrutinee, arms } => {
            visitor.visit_mut_term(&mut *scrutinee);
            arms.iter_mut().for_each(|(_pattern, arm)| {
                // visitor.visit_mut_pattern(pattern); // Issue #1672
                visitor.visit_mut_term(&mut *arm)
            })
        }
        TermKind::Let { pattern: _, arg, body } => {
            // visitor.visit_mut_pattern(pattern); // Issue #1672
            visitor.visit_mut_term(&mut *arg);
            visitor.visit_mut_term(&mut *body)
        }
        TermKind::Projection { lhs, idx: _ } => visitor.visit_mut_term(&mut *lhs),
        TermKind::Old { term } => visitor.visit_mut_term(&mut *term),
        TermKind::Closure { body, .. } => visitor.visit_mut_term(&mut *body),
        TermKind::Reborrow { inner, projections } => {
            visitor.visit_mut_term(&mut *inner);
            visit_projections_mut(projections, |term| visitor.visit_mut_term(term))
        }
        TermKind::Assert { cond } => visitor.visit_mut_term(&mut *cond),
        TermKind::Precondition { params, .. } => {
            params.iter_mut().for_each(|a| visitor.visit_mut_term(a))
        }
        TermKind::Postcondition { params, .. } => {
            params.iter_mut().for_each(|a| visitor.visit_mut_term(a))
        }
    }
}

pub fn visit_projections<V, T>(v: &Projections<V, T>, mut f: impl FnMut(&V)) {
    v.iter().for_each(|elem| {
        if let ProjectionElem::Index(v) = elem {
            f(v)
        }
    })
}

pub fn visit_projections_mut<V, T>(v: &mut Projections<V, T>, mut f: impl FnMut(&mut V)) {
    v.iter_mut().for_each(|elem| {
        if let ProjectionElem::Index(v) = elem {
            f(v)
        }
    })
}
