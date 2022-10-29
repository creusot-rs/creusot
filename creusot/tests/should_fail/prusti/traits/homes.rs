extern crate creusot_contracts;
use creusot_contracts::prusti::*;

pub trait MyModel<X> {
    #[logic(('x) -> 'x)]
    fn model(self) -> X;
}

impl<'a, X: MyModel<Y>, Y> MyModel<Y> for &'a mut X {
    #[logic(('curr) -> 'curr)]
    fn model(self) -> Y {
        X::model(*self)
    }
}
