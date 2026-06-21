extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    type A: Tr;

    #[logic]
    fn f(self) -> Self::A;

    #[logic]
    #[ensures(false)]
    fn g(self) {
        self.f().g()
    }
}

impl Tr for () {
    type A = ();

    #[logic]
    fn f(self) -> () {}
}
