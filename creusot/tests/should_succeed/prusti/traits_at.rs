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
        pearlite!{absurd}
    }
}

#[ensures(result.model() == old(x.model()))]
pub fn test(x: &mut bool) -> bool {
    let res = *x;
    *x = !res;
    res
}