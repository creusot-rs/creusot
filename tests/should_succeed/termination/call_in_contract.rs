extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic]
    fn f() {}
    #[logic]
    fn g();
}

impl Foo for () {
    #[logic]
    #[ensures(Self::f() == ())]
    fn g() {}
}
