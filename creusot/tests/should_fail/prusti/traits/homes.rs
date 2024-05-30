extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait MyModel<X> {
    #[logic('x)]
    fn model(self) -> X;
}

impl<'a, X: MyModel<Y>, Y> MyModel<Y> for &'a mut X {
    #[open]
    #[logic]
    fn model(self) -> Y {
        X::model(*self)
    }
}
