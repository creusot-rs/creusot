#![allow(incomplete_features)]
#![feature(specialization)]

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Foo {
    #[logic]
    fn f();
    #[logic]
    fn g();
}
default impl<T> Foo for T {
    #[logic(open)]
    fn f() {}
    #[logic(open)]
    fn g() {}
}

impl Foo for () {
    #[logic(open)]
    fn g() {
        Self::f();
    }
}
