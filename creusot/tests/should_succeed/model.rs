extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Seven();

impl Model for Seven {
    type ModelTy = Int;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

#[trusted]
#[ensures(@result == 7)]
pub fn seven() -> Seven {
    Seven()
}

pub struct Pair<T, U>(T, U);

impl<T, U> Model for Pair<T, U> {
    type ModelTy = (T, U);
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

#[trusted]
#[ensures(@result == (a, b))]
pub fn pair<T, U>(a: T, b: U) -> Pair<T, U> {
    Pair(a, b)
}
