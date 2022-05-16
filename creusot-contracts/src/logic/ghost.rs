use crate as creusot_contracts;
use crate::logic::*;
use creusot_contracts_proc::*;

pub struct Ghost<T>(*mut T)
where
    T: ?Sized;

impl<T> Model for Ghost<T> {
    type ModelTy = T;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

impl<T> Ghost<T> {
    #[trusted]
    #[ensures(@result == *a)]
    pub fn record(a: &T) -> Ghost<T> {
        panic!()
    }
}
