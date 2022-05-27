extern crate creusot_contracts;

use creusot_contracts::*;

pub struct Vec<T>(std::vec::Vec<T>);
impl<T> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        absurd
    }
}

#[ensures(@x == @*x)]
pub fn test<T>(x: &mut Vec<T>) {}
