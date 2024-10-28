extern crate creusot_contracts;

use creusot_contracts::{logic::Seq, *};

pub struct Vec<T>(pub std::vec::Vec<T>);
impl<T> View for Vec<T> {
    type ViewTy = Seq<T>;
    #[open]
    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        absurd
    }
}

#[ensures(x@ == (*x)@)]
pub fn test<T>(x: &mut Vec<T>) {}
