extern crate creusot_std;

use creusot_std::{logic::Seq, prelude::*};

pub struct Vec<T>(pub std::vec::Vec<T>);
impl<T> View for Vec<T> {
    type ViewTy = Seq<T>;
    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

#[ensures(x@ == (*x)@)]
pub fn test<T>(x: &mut Vec<T>) {}
