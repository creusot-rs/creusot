#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::*;

trait T {
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

fn f(v: Vec<u32>) {
    v.x();
    // **SHOULD NOT** pass since we get the specialized spec for `Vec<u32>`
    proof_assert! { false };
}

fn g<T>(v: Vec<T>) {
    v.x();

    // **SHOULD NOT** pass since we don't get the potentially specializable spec for `Vec<T>`
    proof_assert! { false };
}

fn h(v: Vec<i32>) {
    v.x();
    // **SHOULD** pass since we get the spec for `Vec<T>` applied to `i32` as there is no specialization
    proof_assert! { false };
}
