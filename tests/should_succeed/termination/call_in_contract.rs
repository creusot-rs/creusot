extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Foo {
    #[logic]
    #[open(self)]
    fn f() {}
    #[logic]
    fn g();
}

impl Foo for () {
    #[logic]
    #[ensures(Self::f() == ())]
    #[open(self)]
    fn g() {}
}
