#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::{
    std::{clone::Clone, cmp::PartialEq},
    EqModel, *,
};

#[derive(Clone, PartialEq)]
pub struct Product<A, B> {
    a: A,
    b: B,
}

impl<A, B> EqModel for Product<A, B>
where
    A: EqModel,
    B: EqModel,
{
    type EqModelTy = Product<A::EqModelTy, B::EqModelTy>;

    #[open]
    #[logic]
    fn eq_model(self) -> Self::EqModelTy {
        Product { a: self.a.eq_model(), b: self.b.eq_model() }
    }
}

#[derive(Clone, PartialEq)]
pub enum Sum<A, B> {
    A(A),
    B(B),
}

impl<A: EqModel, B: EqModel> EqModel for Sum<A, B> {
    type EqModelTy = Sum<A::EqModelTy, B::EqModelTy>;

    #[open]
    #[logic]
    fn eq_model(self) -> Self::EqModelTy {
        match self {
            Sum::A(a) => Sum::A(a.eq_model()),
            Sum::B(b) => Sum::B(b.eq_model()),
        }
    }
}

// Resolve derive macro

#[derive(Resolve)]
pub struct Product2<'a, A> {
    a: &'a mut A,
    b: bool,
    c: Vec<u32>,
}

#[derive(Resolve)]
pub enum Sum2<A, B> {
    X(A),
    Y { a: bool, x: B },
}

pub struct List<T> {
    pub elem: T,
    pub tail: Option<Box<List<T>>>,
}

pub struct ListEqModel<T: EqModel> {
    pub elem: <T as EqModel>::EqModelTy,
    pub tail: Option<Box<ListEqModel<T>>>,
}

impl<T: EqModel> EqModel for List<T> {
    type EqModelTy = ListEqModel<T>;

    #[open]
    #[logic]
    fn eq_model(self) -> Self::EqModelTy {
        ListEqModel {
            elem: self.elem.eq_model(),
            tail: match self.tail {
                None => None,
                Some(tail) => Some(Box::new((*tail).eq_model())),
            },
        }
    }
}

pub enum Expr<V> {
    Var(V),
    Add(Box<Expr<V>>, Box<Expr<V>>),
}

pub enum ExprEqModel<V: EqModel> {
    Var(<V as EqModel>::EqModelTy),
    Add(Box<ExprEqModel<V>>, Box<ExprEqModel<V>>),
}

impl<V: EqModel> EqModel for Expr<V> {
    type EqModelTy = ExprEqModel<V>;

    #[open]
    #[logic]
    fn eq_model(self) -> Self::EqModelTy {
        match self {
            Expr::Var(v) => ExprEqModel::Var(v.eq_model()),
            Expr::Add(e1, e2) => {
                ExprEqModel::Add(Box::new((*e1).eq_model()), Box::new((*e2).eq_model()))
            }
        }
    }
}
