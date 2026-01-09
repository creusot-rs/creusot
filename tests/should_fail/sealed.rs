extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn f(self, x: Int) -> Int;

    #[logic(open, sealed)]
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
