#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::{
    std::{clone::Clone, cmp::PartialEq},
    *,
};

#[derive(Clone, PartialEq)]
pub struct Product<A, B> {
    a: A,
    b: B,
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
    a: &'a mut A,
    b: bool,
    c: Vec<u32>,
}

#[derive(Resolve)]
pub enum Sum2<A, B> {
    X(A),
    Y { a: bool, x: B },
}

#[derive(DeepModel)]
pub struct List<T> {
    pub elem: T,
    pub tail: Option<Box<List<T>>>,
}

#[derive(DeepModel)]
pub enum Expr<V> {
    Var(V),
    Add(Box<Expr<V>>, Box<Expr<V>>),
}
