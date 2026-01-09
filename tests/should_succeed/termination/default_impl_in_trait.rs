extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic]
    fn f() {}
    #[logic]
    fn g();
}

pub mod inner {
    use super::*;
    pub trait Bar {
        #[logic(open(super))]
        fn f() {}
        #[logic]
        fn g();
    }
}

impl Foo for () {
    #[logic]
    fn g() {
        <Self as Foo>::f();
    }
}

impl<T> Foo for Box<T> {
    #[logic]
    fn g() {
        <Self as Foo>::f();
    }
}

impl inner::Bar for () {
    #[logic]
    fn g() {
        <Self as inner::Bar>::f();
    }
}
