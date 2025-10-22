#![allow(incomplete_features)]
#![feature(specialization)]

extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub trait Foo {
    #[logic]
    fn f();
    #[logic]
    fn g();
}
default impl<T> Foo for T {
    #[logic(open)]
    fn f() {
        h();
    }
    #[logic(open)]
    fn g() {}
}
impl Foo for i32 {
    #[logic(open)]
    fn g() {
        Self::f();
    }
}

#[logic(open)]
pub fn h() {
    <i32 as Foo>::g();
}
