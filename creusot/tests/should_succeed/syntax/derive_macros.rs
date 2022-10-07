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

impl<A, B> DeepModel for Product<A, B>
where
    A: DeepModel,
    B: DeepModel,
{
    type DeepModelTy = Product<A::DeepModelTy, B::DeepModelTy>;

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

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Sum::A(a) => Sum::A(a.deep_model()),
            Sum::B(b) => Sum::B(b.deep_model()),
        }
    }
}
