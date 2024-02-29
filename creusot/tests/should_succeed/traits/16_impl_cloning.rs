extern crate creusot_contracts;

use creusot_contracts::{logic::Seq, *};

pub struct Vec<T>(std::vec::Vec<T>);
impl<T> ShallowModel for Vec<T> {
    type ShallowModelTy = Seq<T>;
    #[open]
    #[logic]
    #[trusted]
    fn shallow_model(self) -> Self::ShallowModelTy {
        absurd
    }
}

#[ensures(x@ == (*x)@)]
pub fn test<T>(x: &mut Vec<T>) {}
