use std::collections::HashMap;

use rustc_middle::mir::{self, Local};
use std::collections::HashSet;

use crate::translation::{
    fmir,
    pearlite::{super_visit_term, Term, TermKind, TermVisitor},
};

pub(crate) struct LocalUsage<'a, 'tcx> {
    locals: &'a fmir::LocalDecls<'tcx>,
    pub(crate) usages: HashMap<Local, Usage>,
}

#[derive(Clone, Copy, Default, Debug, PartialEq, Eq)]
pub(crate) enum ZeroOneMany {
    #[default]
    Zero,
    One(Whole),
    Many,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Whole {
    Whole,
    Part,
}

impl ZeroOneMany {
    fn inc(&mut self, whole: Whole) {
        *self = match self {
            ZeroOneMany::Zero => ZeroOneMany::One(whole),
            ZeroOneMany::One(_) => ZeroOneMany::Many,
            ZeroOneMany::Many => ZeroOneMany::Many,
        }
    }
}

#[derive(Clone, Copy, Default, Debug)]
pub(crate) struct Usage {
    write: ZeroOneMany,
    read: ZeroOneMany,
    temp_var: bool,
}

pub(crate) fn gather_usage(b: &fmir::Body) -> HashMap<Local, Usage> {
    let mut usage = LocalUsage { locals: &b.locals, usages: HashMap::new() };

    usage.visit_body(b);
    usage.usages
}

impl<'a, 'tcx> LocalUsage<'a, 'tcx> {
    pub(crate) fn visit_body(&mut self, b: &fmir::Body<'tcx>) {
        b.blocks.values().for_each(|b| self.visit_block(b));
    }

    fn visit_block(&mut self, b: &fmir::Block<'tcx>) {
        b.stmts.iter().for_each(|s| self.visit_statement(s));
        self.visit_terminator(&b.terminator);
    }

    fn visit_terminator(&mut self, t: &fmir::Terminator<'tcx>) {
        match t {
            fmir::Terminator::Switch(e, _) => self.visit_expr(e),
            // fmir::Terminator::Return => {self.read(0u32.into(), true); self.read(0u32.into(), true);}
            _ => {}
        }
    }

    fn visit_statement(&mut self, b: &fmir::Statement<'tcx>) {
        match b {
            fmir::Statement::Assignment(p, r) => {
                self.write_place(p);
                self.visit_rvalue(r)
            }
            fmir::Statement::Resolve(_, _, p) => {
                self.read_place(p);
                self.read_place(p)
            }
            fmir::Statement::Assertion { cond, msg: _ } => {
                // Make assertions stop propagation because it would require Expr -> Term translation
                self.visit_term(cond);
                self.visit_term(cond);
            }
            fmir::Statement::Invariant(t) => self.visit_term(t),
            fmir::Statement::Variant(t) => self.visit_term(t),
        }
    }

    fn visit_rvalue(&mut self, r: &fmir::RValue<'tcx>) {
        match r {
            fmir::RValue::Ghost(t) => self.visit_term(t),
            fmir::RValue::Borrow(p) => {
                self.read_place(p);
                self.read_place(p)
            }
            fmir::RValue::Expr(e) => self.visit_expr(e),
        }
    }

    // fn visit_term(&mut self, t: &Term<'tcx>) {}

    fn visit_expr(&mut self, e: &fmir::Expr<'tcx>) {
        match e {
            fmir::Expr::Move(p) => self.read_place(p),
            fmir::Expr::Copy(p) => self.read_place(p),
            fmir::Expr::BinOp(_, _, l, r) => {
                self.visit_expr(l);
                self.visit_expr(r)
            }
            fmir::Expr::UnaryOp(_, _, e) => self.visit_expr(e),
            fmir::Expr::Constructor(_, _, es) => es.iter().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Call(_, _, es) => es.iter().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Constant(t) => self.visit_term(t),
            fmir::Expr::Cast(e, _, _) => self.visit_expr(e),
            fmir::Expr::Tuple(es) => es.iter().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Span(_, e) => self.visit_expr(e),
            fmir::Expr::Len(e) => self.visit_expr(e),
            fmir::Expr::Array(es) => es.iter().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Repeat(l, r) => {
                self.visit_expr(l);
                self.visit_expr(r)
            }
        }
    }

    fn read_place(&mut self, p: &mir::Place<'tcx>) {
        self.read(p.local, p.projection.is_empty());
        p.projection.iter().for_each(|p| match p {
            mir::ProjectionElem::Index(l) => self.read(l, true),
            _ => {}
        })
    }

    fn write_place(&mut self, p: &mir::Place<'tcx>) {
        self.write(p.local, p.projection.is_empty());
        p.projection.iter().for_each(|p| match p {
            mir::ProjectionElem::Index(l) => self.read(l, true),
            _ => {}
        })
    }

    fn read(&mut self, local: Local, whole: bool) {
        self.usages
            .entry(local)
            .or_insert_with(|| Usage {
                temp_var: self.locals[&local].0.is_anon(),
                ..Default::default()
            })
            .read
            .inc(if whole { Whole::Whole } else { Whole::Part })
    }

    fn write(&mut self, local: Local, whole: bool) {
        self.usages
            .entry(local)
            .or_insert_with(|| Usage {
                temp_var: self.locals[&local].0.is_anon(),
                ..Default::default()
            })
            .write
            .inc(if whole { Whole::Whole } else { Whole::Part })
    }
}

impl<'a, 'tcx> TermVisitor<'tcx> for LocalUsage<'a, 'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        match term.kind {
            TermKind::Var(v) => {
                let l = self.locals.iter().find(|(_, a)| a.0.symbol() == v);
                l.map(|(l, _)| self.read(*l, true));
            }
            _ => super_visit_term(term, self),
        }
    }
}

struct SimplePropagator<'tcx> {
    usage: HashMap<Local, Usage>,
    prop: HashMap<Local, fmir::Expr<'tcx>>,
    dead: HashSet<Local>,
}

pub(crate) fn simplify_fmir<'tcx>(usage: HashMap<Local, Usage>, body: &mut fmir::Body) {
    SimplePropagator { usage, prop: HashMap::new(), dead: HashSet::new() }.visit_body(body);
}
impl<'tcx> SimplePropagator<'tcx> {
    fn visit_body(&mut self, b: &mut fmir::Body<'tcx>) {
        for b in b.blocks.values_mut() {
            self.visit_block(b)
        }

        b.locals.retain(|l, _| !self.dead.contains(&l) && self.usage.contains_key(&l));

        assert!(self.prop.is_empty(), "some values were not properly propagated {:?}", self.prop)
    }

    fn visit_block(&mut self, b: &mut fmir::Block<'tcx>) {
        let mut out_stmts = Vec::with_capacity(b.stmts.len());

        for mut s in std::mem::take(&mut b.stmts) {
            self.visit_statement(&mut s);
            match s {
                fmir::Statement::Assignment(l, fmir::RValue::Expr(r))
                    if self.should_propagate(l.local) && !r.is_call() => {
                      self.prop.insert(l.local, r);
                      self.dead.insert(l.local);
                    }
                fmir::Statement::Resolve(_,_, p) => {
                  if let Some(l) = p.as_local() && self.dead.contains(&l) {
                  } else {
                    out_stmts.push(s)
                  }
                }
                _ => out_stmts.push(s),
            }
        }
        b.stmts = out_stmts;

        match &mut b.terminator {
            fmir::Terminator::Goto(_) => {}
            fmir::Terminator::Switch(e, _) => self.visit_expr(e),
            fmir::Terminator::Return => {}
            fmir::Terminator::Abort => {}
        }
    }

    fn visit_statement(&mut self, s: &mut fmir::Statement<'tcx>) {
        match s {
            fmir::Statement::Assignment(_, r) => self.visit_rvalue(r),
            fmir::Statement::Resolve(_, _, p) => {
              if let Some(l) = p.as_local() && self.dead.contains(&l) {

              }
            }
            fmir::Statement::Assertion { cond, msg: _ } => self.visit_term(cond),
            fmir::Statement::Invariant(t) => self.visit_term(t),
            fmir::Statement::Variant(t) => self.visit_term(t),
        }
    }

    fn visit_rvalue(&mut self, r: &mut fmir::RValue<'tcx>) {
        match r {
            fmir::RValue::Ghost(t) => self.visit_term(t),
            fmir::RValue::Borrow(p) => {
                assert!(self.prop.get(&p.local).is_none(), "Trying to propagate borrowed variable")
            }
            fmir::RValue::Expr(e) => self.visit_expr(e),
        }
    }

    fn visit_expr(&mut self, e: &mut fmir::Expr<'tcx>) {
        match e {
            fmir::Expr::Move(p) | fmir::Expr::Copy(p) => {
              if let Some(l) = p.as_local() && let Some(v) = self.prop.remove(&l) {
                *e = v;
              }
            },
            fmir::Expr::BinOp(_, _, l, r) => {
                self.visit_expr(l);
                self.visit_expr(r)
            }
            fmir::Expr::UnaryOp(_, _, e) => self.visit_expr(e),
            fmir::Expr::Constructor(_, _, es) => es.iter_mut().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Call(_, _, es) => es.iter_mut().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Constant(t) => self.visit_term(t),
            fmir::Expr::Cast(e, _, _) => self.visit_expr(e),
            fmir::Expr::Tuple(es) => es.iter_mut().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Span(_, e) => self.visit_expr(e),
            fmir::Expr::Len(e) => self.visit_expr(e),
            fmir::Expr::Array(es) => es.iter_mut().for_each(|e| self.visit_expr(e)),
            fmir::Expr::Repeat(l, r) => {
                self.visit_expr(l);
                self.visit_expr(r)
            }
        }
    }

    fn visit_term(&mut self, _t: &mut Term<'tcx>) {
        // TODO: Find a way to propagate Expr into Term
        //   _t.subst_with(|s| {
        //     let x = self.usage.iter().find(|(k, _)| LocalIdent::anon(k).symbol() == s );

        //     x.and_then(|l| self.prop.remove(l))
        //   })
    }

    fn should_propagate(&self, l: Local) -> bool {
        self.usage
            .get(&l)
            .map(|u| {
                u.read == ZeroOneMany::One(Whole::Whole)
                    && u.write == ZeroOneMany::One(Whole::Whole)
                    && u.temp_var
            })
            .unwrap_or(false)
    }
}
