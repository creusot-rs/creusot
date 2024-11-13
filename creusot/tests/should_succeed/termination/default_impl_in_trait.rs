extern crate creusot_contracts;
use creusot_contracts::*;

pub trait Foo {
    #[logic]
    #[open(self)]
    fn f() {}
    #[logic]
    fn g();
}

pub mod inner {
    use super::*;
    pub trait Bar {
        #[logic]
        #[open(super)]
        fn f() {}
        #[logic]
        fn g();
    }
}

impl Foo for () {
    #[logic]
    #[open(self)]
    fn g() {
        <Self as Foo>::f();
    }
}

impl<T> Foo for Box<T> {
    #[logic]
    #[open(self)]
    fn g() {
        <Self as Foo>::f();
    }
}

impl inner::Bar for () {
    #[logic]
    #[open(self)]
    fn g() {
        <Self as inner::Bar>::f();
    }
}
