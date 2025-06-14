extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Tr {
    #[logic]
    fn f(self, x: Int) -> Int;

    #[logic(sealed)]
    #[open]
    fn g(self, x: Int) -> Int {
        self.f(x) + 1
    }
}

impl Tr for Int {
    #[logic]
    fn f(self, x: Int) -> Int {
        self + x
    }

    #[logic]
    fn g(self, x: Int) -> Int {
        x
    }
}
