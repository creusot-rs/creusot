extern crate creusot_contracts;
use creusot_contracts::*;

pub struct Seven();

impl ShallowModel for Seven {
    type ShallowModelTy = Int;

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

#[trusted]
#[ensures(@result == 7)]
pub fn seven() -> Seven {
    Seven()
}

pub struct Pair<T, U>(T, U);

impl<T, U> ShallowModel for Pair<T, U> {
    type ShallowModelTy = (T, U);

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

#[trusted]
#[ensures(@result == (a, b))]
pub fn pair<T, U>(a: T, b: U) -> Pair<T, U> {
    Pair(a, b)
}
