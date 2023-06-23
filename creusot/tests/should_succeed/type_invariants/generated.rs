#![feature(min_specialization)]
extern crate creusot_contracts;
use creusot_contracts::{
    invariant::{self, Invariant},
    *,
};

pub struct Sum10(i32, i32);

impl Invariant for Sum10 {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        pearlite! { self.0@ + self.1@ == 10 }
    }
}

pub enum Foo<'a, T> {
    A { f1: &'a mut Sum10, f2: usize },
    B(T),
}

pub fn use_foo<'a>(x: Foo<'a, (Foo<'a, u32>, &'a mut Sum10)>) {
    proof_assert!(invariant::inv(x));
}
