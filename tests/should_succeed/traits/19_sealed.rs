extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub trait Tr {
    #[logic]
    fn f(self, x: Int) -> Int;

    #[logic(open, sealed)]
    fn g(self, x: Int) -> Int {
        self.f(x) + 1
    }
}

#[ensures(x.g(y) == x.f(y) + 1)]
pub fn p<T: Tr>(x: T, y: Int) {}
