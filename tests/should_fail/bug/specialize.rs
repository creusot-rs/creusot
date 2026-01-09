// WHY3PROVE
#![feature(min_specialization)]
extern crate creusot_std;
use creusot_std::prelude::*;

pub trait T {
    fn x(self);
}

impl<U> T for Vec<U> {
    #[trusted]
    #[ensures(false)]
    default fn x(self) {}
}

impl T for Vec<u32> {
    #[trusted]
    #[ensures(true)]
    fn x(self) {}
}

pub fn f(v: Vec<u32>) {
    v.x();
    // **SHOULD NOT** pass since we get the specialized spec for `Vec<u32>`
    proof_assert! { false };
}

pub fn g<T>(v: Vec<T>) {
    v.x();

    // **SHOULD NOT** pass since we don't get the potentially specializable spec for `Vec<T>`
    proof_assert! { false };
}

pub fn h(v: Vec<i32>) {
    v.x();
    // **SHOULD** pass since we get the spec for `Vec<T>` applied to `i32` as there is no specialization
    proof_assert! { false };
}
