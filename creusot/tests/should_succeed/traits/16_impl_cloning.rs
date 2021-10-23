extern crate creusot_contracts;

use creusot_contracts::*;

struct Vec<T>(std::vec::Vec<T>);
impl<T: ?Sized> Model for Vec<T> {
    type ModelTy = Seq<T>;
    #[logic]
    #[trusted]
    fn model(self) -> Self::ModelTy {
        panic!()
    }
}

#[ensures(@x === @*x)]
fn test<T>(x: &mut Vec<T>) {}
