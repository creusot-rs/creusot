extern crate creusot_contracts;
use creusot_contracts::{
    derive::{Clone, PartialEq},
    *,
};

#[derive(Clone, PartialEq)]
pub struct Product<A, B> {
    a: A,
    b: B,
}

impl<A, B> Model for Product<A, B>
where
    A: Model,
    B: Model,
{
    type ModelTy = Product<A::ModelTy, B::ModelTy>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        Product { a: self.a.model(), b: self.b.model() }
    }
}

#[derive(Clone, PartialEq)]
pub enum Sum<A, B> {
    A(A),
    B(B),
}

impl<A: Model, B: Model> Model for Sum<A, B> {
    type ModelTy = Sum<A::ModelTy, B::ModelTy>;

    #[logic]
    fn model(self) -> Self::ModelTy {
        match self {
            Sum::A(a) => Sum::A(a.model()),
            Sum::B(b) => Sum::B(b.model()),
        }
    }
}
