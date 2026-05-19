#![feature(trait_alias)]
extern crate creusot_std;
use creusot_std::prelude::check;

pub trait Tr {
    #[check(terminates)]
    fn f(self);
}

// Test that the termination checker correctly handles trait synonyms
// (this should just work because the rustc API provides already expanded trait bounds)
pub trait Syn = Tr + Clone;

#[derive(Clone)]
pub struct A<T>(T);

impl<T: Syn> Tr for A<T> {
    #[check(terminates)]
    fn f(self) {
        self.0.f();
    }
}

#[derive(Clone)]
pub struct B;

impl Tr for B {
    #[check(terminates)]
    fn f(self) {
        A(A(A(self))).f()
    }
}
