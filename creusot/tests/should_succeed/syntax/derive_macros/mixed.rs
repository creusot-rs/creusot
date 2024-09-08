#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::{
    std::{clone::Clone, cmp::PartialEq},
    *,
};

#[derive(Clone, PartialEq)]
pub struct Product<A, B> {
    pub a: A,
    pub b: B,
}

impl<A, B> DeepModel for Product<A, B>
where
    A: DeepModel,
    B: DeepModel,
{
    type DeepModelTy = Product<A::DeepModelTy, B::DeepModelTy>;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        Product { a: self.a.deep_model(), b: self.b.deep_model() }
    }
}

#[derive(Clone, PartialEq)]
pub enum Sum<A, B> {
    A(A),
    B(B),
}

impl<A: DeepModel, B: DeepModel> DeepModel for Sum<A, B> {
    type DeepModelTy = Sum<A::DeepModelTy, B::DeepModelTy>;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Sum::A(a) => Sum::A(a.deep_model()),
            Sum::B(b) => Sum::B(b.deep_model()),
        }
    }
}

// Resolve derive macro

#[derive(Resolve)]
pub struct Product2<'a, A> {
    pub a: &'a mut A,
    pub b: bool,
    pub c: Vec<u32>,
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

pub struct ListDeepModel<T: DeepModel> {
    pub elem: <T as DeepModel>::DeepModelTy,
    pub tail: Option<Box<ListDeepModel<T>>>,
}

impl<T: DeepModel> DeepModel for List<T> {
    type DeepModelTy = ListDeepModel<T>;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        ListDeepModel {
            elem: self.elem.deep_model(),
            tail: match self.tail {
                None => None,
                Some(tail) => Some(Box::new((*tail).deep_model())),
            },
        }
    }
}

pub enum Expr<V> {
    Var(V),
    Add(Box<Expr<V>>, Box<Expr<V>>),
}

pub enum ExprDeepModel<V: DeepModel> {
    Var(<V as DeepModel>::DeepModelTy),
    Add(Box<ExprDeepModel<V>>, Box<ExprDeepModel<V>>),
}

impl<V: DeepModel> DeepModel for Expr<V> {
    type DeepModelTy = ExprDeepModel<V>;

    #[open]
    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Expr::Var(v) => ExprDeepModel::Var(v.deep_model()),
            Expr::Add(e1, e2) => {
                ExprDeepModel::Add(Box::new((*e1).deep_model()), Box::new((*e2).deep_model()))
            }
        }
    }
}
