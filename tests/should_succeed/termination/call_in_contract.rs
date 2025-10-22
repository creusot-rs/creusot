extern crate creusot_contracts;
use creusot_contracts::prelude::*;

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
