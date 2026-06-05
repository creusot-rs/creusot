extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    type A: Tr;

    fn f(self) -> Self::A;

    #[logic]
    #[ensures(false)]
    fn g(self) {
        self.f().g()
    }
}

impl Tr for () {
    type A = ();
    fn f(self) -> () {}
}
