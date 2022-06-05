#![feature(allocator_api)]

extern crate creusot_contracts;

use creusot_contracts::{ensures, extern_spec, invariant, logic, predicate, requires};

pub enum Expr {
    IfThenElse { c: Box<Expr>, t: Box<Expr>, e: Box<Expr> },
    Var { v: usize },
    True,
    False,
}

use std::alloc::Allocator;
extern_spec! {
    mod std {
        mod boxed {
            impl<T : Clone, A : Allocator + Clone> Clone for Box<T, A> {
                #[ensures(result == *self)]
                fn clone(&self) -> Self;
            }
        }
    }
}

impl Clone for Expr {
    #[ensures(*self == result)]
    fn clone(&self) -> Self {
        match self {
            Expr::IfThenElse { c, t, e } => {
                Expr::IfThenElse { c: c.clone(), t: t.clone(), e: e.clone() }
            }
            Expr::Var { v } => Expr::Var { v: *v },
            Expr::True => Expr::True,
            Expr::False => Expr::False,
        }
    }
}

impl From<usize> for Expr {
    fn from(a: usize) -> Self {
        Self::variable(a)
    }
}

impl From<bool> for Expr {
    fn from(b: bool) -> Self {
        if b {
            Self::True
        } else {
            Self::False
        }
    }
}

impl Expr {
    #[ensures(result == Expr::IfThenElse { c: Box::new(c), t: Box::new(t), e: Box::new(e) })]
    pub fn ite(c: Expr, t: Expr, e: Expr) -> Self {
        Self::IfThenElse { c: Box::new(c), t: Box::new(t), e: Box::new(e) }
    }

    pub fn variable(v: usize) -> Self {
        Self::Var { v }
    }

    #[requires(self.is_normalized())]
    #[requires(a.is_normalized())]
    #[requires(b.is_normalized())]
    #[ensures(result.is_normalized())]
    pub fn transpose(self, a: Self, b: Self) -> Self {
        match self {
            Self::IfThenElse { c, t, e } => Self::IfThenElse {
                c,
                t: Box::new(t.transpose(a.clone(), b.clone())),
                e: Box::new(e.transpose(a, b)),
            },
            Self::Var { v } => {
                Self::IfThenElse { c: Box::new(self), t: Box::new(a), e: Box::new(b) }
            }
            Self::True => a,
            Self::False => b,
        }
    }

    #[predicate]
    fn is_normalized(self) -> bool {
        match self {
            Expr::IfThenElse { c, t, e } => match *c {
                Expr::IfThenElse { .. } => false,
                _ => t.is_normalized() && e.is_normalized(),
            },
            Expr::Var { .. } => true,
            Expr::True => true,
            Expr::False => true,
        }
    }

    #[ensures(result.is_normalized())]
    pub fn normalize(&self) -> Self {
        match self {
            Expr::IfThenElse { c, t, e } => {
                let cp = c.normalize();
                let tp = t.normalize();
                let ep = e.normalize();
                cp.transpose(tp, ep)
            }
            e => e.clone(),
        }
    }
}
