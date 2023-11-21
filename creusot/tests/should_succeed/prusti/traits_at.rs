#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait MyModel {
    type ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy;
}

impl<'a, X: MyModel> MyModel for &'a mut X {
    type ModelTy = X::ModelTy;
    #[logic]
    fn model(self) -> Self::ModelTy {
        X::model(*self)
    }
}

impl<'a> MyModel for bool{
    type ModelTy = bool;
    #[logic('_)]
    fn model(self) -> bool {
        self
    }
}

struct Wrap<T>(T);
impl<T> MyModel for Wrap<T> {
    type ModelTy = T;

    #[logic]
    fn model(self) -> Self::ModelTy {
        self.0
    }
}

#[ensures(result.model() == old(x.model()))]
pub fn test(x: &mut bool) -> bool {
    let res = *x;
    *x = !res;
    res
}

#[ensures(result == x.model())]
pub fn test2(x: Wrap<bool>) -> bool {
    x.0
}