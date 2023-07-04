extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait MyModel<T> {
    #[logic(('curr) -> 'curr)]
    fn model(self) -> T;
}

impl<'a, X: MyModel<Y>, Y> MyModel<Y> for &'a mut X {
    #[logic(('curr) -> 'curr)]
    fn model(self) -> Y {
        X::model(*self)
    }
}

impl<'a> MyModel<bool> for bool{
    #[logic(('_) -> '_)]
    fn model(self) -> bool {
        if self {true} else {false}
    }
}

#[ensures(result.model() == old(x.model()))]
pub fn test(x: &mut bool) -> bool {
    let res = *x;
    *x = !res;
    res
}

pub struct Wrapper<T>(T);

impl<T> MyModel<T> for Wrapper<T> {
    #[logic(('x) -> 'x)]
    fn model(self) -> T {
        self.0
    }
}

#[ensures(*result == old(*x.model()))]
#[after_expiry(*x.model() == *result)]
pub fn test2(x: Wrapper<&mut u32>) -> &mut u32 {
    x.0
}