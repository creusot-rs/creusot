use std::collections::HashMap;

use rustc_middle::mir::{self};
use rustc_span::Symbol;
use std::collections::HashSet;

use crate::translation::{
    fmir::*,
    pearlite::{super_visit_term, Term, TermKind, TermVisitor},
};

pub mod invariants;

pub use invariants::*;

pub(crate) struct LocalUsage<'a, 'tcx> {
    locals: &'a LocalDecls<'tcx>,
    pub(crate) usages: HashMap<Symbol, Usage>,
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
    // Is this local used in a place where we need a `Term`?
    used_in_pure_ctx: bool,
    // Is this local being used in a move chain as in: _x = _y
    is_move_chain: bool,
}

pub(crate) fn gather_usage(b: &Body) -> HashMap<Symbol, Usage> {
    let mut usage = LocalUsage { locals: &b.locals, usages: HashMap::new() };

    usage.visit_body(b);
    usage.usages
}

impl<'a, 'tcx> LocalUsage<'a, 'tcx> {
    pub(crate) fn visit_body(&mut self, b: &Body<'tcx>) {
        b.blocks.values().for_each(|b| self.visit_block(b));
    }

    fn visit_block(&mut self, b: &Block<'tcx>) {
        b.invariants.iter().for_each(|t| self.visit_term(t));
        b.variant.iter().for_each(|t| self.visit_term(t));
        b.stmts.iter().for_each(|s| self.visit_statement(s));
        self.visit_terminator(&b.terminator);
    }

    fn visit_terminator(&mut self, t: &Terminator<'tcx>) {
        match t {
            Terminator::Switch(e, _) => self.visit_operand(e),
            Terminator::Return => {
                self.read(Symbol::intern("_0"), true);
                self.read(Symbol::intern("_0"), true);
            }
            _ => {}
        }
    }

    fn visit_statement(&mut self, b: &Statement<'tcx>) {
        match b {
            Statement::Assignment(p, r, _) => {
                self.write_place(p);
                if let RValue::Operand(_) = r {
                    self.move_chain(p.local);
                }
                self.visit_rvalue(r)
            }
            Statement::Resolve { pl, .. } => {
                self.read_place(pl);
                self.read_place(pl)
            }
            Statement::Assertion { cond, msg: _ } => {
                // Make assertions stop propagation because it would require Expr -> Term translation
                self.visit_term(cond);
                self.visit_term(cond);
            }
            Statement::AssertTyInv { pl, .. } => self.read_place(pl),
            Statement::Call(dest, _, _, args, _) => {
                self.write_place(dest);
                args.iter().for_each(|a| self.visit_operand(a));
            }
        }
    }

    fn visit_rvalue(&mut self, r: &RValue<'tcx>) {
        match r {
            RValue::Ghost(t) => self.visit_term(t),
            RValue::Borrow(_, p, _) => {
                self.read_place(p);
                self.read_place(p)
            }
            RValue::Operand(op) => match op {
                Operand::Move(p) | Operand::Copy(p) => {
                    self.read_place(p);
                    // self.move_chain(p.local);
                }
                Operand::Constant(t) => self.visit_term(t),
                Operand::Promoted(_, _) => {}
            },
            RValue::BinOp(_, l, r) => {
                self.visit_operand(l);
                self.visit_operand(r)
            }
            RValue::UnaryOp(_, e) => self.visit_operand(e),
            RValue::Constructor(_, _, es) => es.iter().for_each(|e| self.visit_operand(e)),
            RValue::Cast(e, _, _) => self.visit_operand(e),
            RValue::Tuple(es) => es.iter().for_each(|e| self.visit_operand(e)),
            RValue::Len(e) => self.visit_operand(e),
            RValue::Array(es) => es.iter().for_each(|e| self.visit_operand(e)),
            RValue::Repeat(l, r) => {
                self.visit_operand(l);
                self.visit_operand(r)
            }
        }
    }

    // fn visit_term(&mut self, t: &Term<'tcx>) {}

    fn visit_operand(&mut self, op: &Operand<'tcx>) {
        match op {
            Operand::Move(p) => self.read_place(p),
            Operand::Copy(p) => self.read_place(p),
            Operand::Constant(t) => self.visit_term(t),
            Operand::Promoted(_, _) => {}
        }
    }

    fn read_place(&mut self, p: &Place<'tcx>) {
        self.read(p.local, p.projection.is_empty());
        p.projection.iter().for_each(|p| match p {
            mir::ProjectionElem::Index(l) => self.read(*l, true),
            _ => {}
        })
    }

    fn write_place(&mut self, p: &Place<'tcx>) {
        self.write(p.local, p.projection.is_empty());
        p.projection.iter().for_each(|p| match p {
            mir::ProjectionElem::Index(l) => self.read(*l, true),
            _ => {}
        })
    }

    fn move_chain(&mut self, local: Symbol) {
        if let Some(usage) = self.get(local) {
            usage.is_move_chain = true;
        }
    }

    fn read(&mut self, local: Symbol, whole: bool) {
        if let Some(usage) = self.get(local) {
            usage.read.inc(if whole { Whole::Whole } else { Whole::Part })
        };
    }

    fn get(&mut self, local: Symbol) -> Option<&mut Usage> {
        if !self.locals.contains_key(&local) {
            return None;
        }

        Some(
            self.usages.entry(local).or_insert_with(|| Usage {
                temp_var: self.locals[&local].temp,
                ..Default::default()
            }),
        )
    }
    fn write(&mut self, local: Symbol, whole: bool) {
        if let Some(usage) = self.get(local) {
            usage.write.inc(if whole { Whole::Whole } else { Whole::Part })
        };
    }

    fn pure(&mut self, local: Symbol) {
        if let Some(usage) = self.get(local) {
            usage.used_in_pure_ctx = true
        };
    }
}

impl<'a, 'tcx> TermVisitor<'tcx> for LocalUsage<'a, 'tcx> {
    fn visit_term(&mut self, term: &Term<'tcx>) {
        match term.kind {
            TermKind::Var(v) => {
                self.pure(v);
                self.read(v, true);
            }
            _ => super_visit_term(term, self),
        }
    }
}

struct SimplePropagator<'tcx> {
    /// Tracks how many reads and writes each variable has
    usage: HashMap<Symbol, Usage>,
    prop: HashMap<Symbol, Operand<'tcx>>,
    dead: HashSet<Symbol>,
}

pub(crate) fn simplify_fmir<'tcx>(usage: HashMap<Symbol, Usage>, body: &mut Body) {
    SimplePropagator { usage, prop: HashMap::new(), dead: HashSet::new() }.visit_body(body);
}
impl<'tcx> SimplePropagator<'tcx> {
    fn visit_body(&mut self, b: &mut Body<'tcx>) {
        for b in b.blocks.values_mut() {
            self.visit_block(b)
        }

        b.locals.retain(|l, _| !self.dead.contains(&l) && self.usage.contains_key(&l));

        assert!(self.prop.is_empty(), "some values were not properly propagated {:?}", self.prop)
    }

    fn visit_block(&mut self, b: &mut Block<'tcx>) {
        let mut out_stmts = Vec::with_capacity(b.stmts.len());

        for mut s in std::mem::take(&mut b.stmts) {
            self.visit_statement(&mut s);
            match s {
                Statement::Assignment(l, RValue::Operand(op), _)
                    // we do not propagate calls to avoid moving them after the resolve of their arguments
                    if self.should_propagate(l.local) && !self.usage[&l.local].used_in_pure_ctx => {
                      self.prop.insert(l.local, op);
                      self.dead.insert(l.local);
                    }
                Statement::Assignment(_, RValue::Ghost(_), _) => {
                    out_stmts.push(s)
                }
                Statement::Assignment(ref l, ref r, _) if self.should_erase(l.local) && r.is_pure() => {
                      self.dead.insert(l.local);
                }
                Statement::Resolve{ pl: ref p, .. } => {
                  if let Some(l) = p.as_symbol() && self.dead.contains(&l) {
                  } else {
                    out_stmts.push(s)
                  }
                }
                _ => out_stmts.push(s),
            }
        }
        b.stmts = out_stmts;

        match &mut b.terminator {
            Terminator::Goto(_) => {}
            Terminator::Switch(e, _) => self.visit_operand(e),
            Terminator::Return => {}
            Terminator::Abort(_) => {}
        }
    }

    fn visit_statement(&mut self, s: &mut Statement<'tcx>) {
        match s {
            Statement::Assignment(_, r, _) => self.visit_rvalue(r),
            Statement::Resolve { pl, .. } => {
                if let Some(l) = pl.as_symbol()
                    && self.dead.contains(&l)
                {}
            }
            Statement::Assertion { cond, msg: _ } => self.visit_term(cond),
            Statement::Call(_, _, _, args, _) => {
                args.iter_mut().for_each(|a| self.visit_operand(a))
            }
            Statement::AssertTyInv { .. } => {}
        }
    }

    fn visit_rvalue(&mut self, r: &mut RValue<'tcx>) {
        match r {
            RValue::Ghost(t) => self.visit_term(t),
            RValue::Borrow(_, p, _) => {
                assert!(self.prop.get(&p.local).is_none(), "Trying to propagate borrowed variable")
            }
            RValue::Operand(op) => self.visit_operand(op),
            RValue::BinOp(_, l, r) => {
                self.visit_operand(l);
                self.visit_operand(r)
            }
            RValue::UnaryOp(_, e) => self.visit_operand(e),
            RValue::Constructor(_, _, es) => es.iter_mut().for_each(|e| self.visit_operand(e)),
            RValue::Cast(e, _, _) => self.visit_operand(e),
            RValue::Tuple(es) => es.iter_mut().for_each(|e| self.visit_operand(e)),
            RValue::Len(e) => self.visit_operand(e),
            RValue::Array(es) => es.iter_mut().for_each(|e| self.visit_operand(e)),
            RValue::Repeat(l, r) => {
                self.visit_operand(l);
                self.visit_operand(r)
            }
        }
    }

    fn visit_operand(&mut self, op: &mut Operand<'tcx>) {
        match op {
            Operand::Move(p) | Operand::Copy(p) => {
                if let Some(l) = p.as_symbol()
                    && let Some(v) = self.prop.remove(&l)
                {
                    *op = v;
                }
            }
            Operand::Constant(_) => {}
            Operand::Promoted(_, _) => {}
        }
    }

    fn visit_term(&mut self, _t: &mut Term<'tcx>) {
        // TODO: Find a way to propagate Expr into Term
        //   _t.subst_with(|s| {
        //     let x = self.usage.iter().find(|(k, _)| LocalIdent::anon(k).symbol() == s );

        //     x.and_then(|l| self.prop.remove(l))
        //   })
    }

    fn should_propagate(&self, l: Symbol) -> bool {
        self.usage
            .get(&l)
            .map(|u| {
                u.read == ZeroOneMany::One(Whole::Whole)
                    && u.write == ZeroOneMany::One(Whole::Whole)
                    && u.temp_var
                    && u.is_move_chain
            })
            .unwrap_or(false)
    }

    fn should_erase(&self, l: Symbol) -> bool {
        self.usage
            .get(&l)
            .map(|u| {
                u.read == ZeroOneMany::Zero && matches!(u.write, ZeroOneMany::One(_)) && u.temp_var
            })
            .unwrap_or(false)
    }
}
