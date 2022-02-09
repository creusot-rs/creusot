extern crate creusot_contracts;

use creusot_contracts::*;

struct Vec<T>(std::vec::Vec<T>);
impl<T> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        std::process::abort()
    }
}

#[ensures(@x === @*x)]
fn test<T>(x: &mut Vec<T>) {}
