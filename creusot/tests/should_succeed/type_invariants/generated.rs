#![allow(incomplete_features)]
#![feature(specialization)]
extern crate creusot_contracts;
use creusot_contracts::{invariant, *};

pub struct Sum10(i32, i32);

impl invariant::UserInv for Sum10 {
    #[predicate]
    #[open]
    fn user_inv(self) -> bool {
        pearlite! { self.0@ + self.1@ == 10 }
    }
}

pub enum Foo<'a, T> {
    A { f1: &'a mut Sum10, f2: usize },
    B(T),
}

#[requires(invariant::inv(x))]
pub fn use_foo<'a>(x: Foo<'a, (Foo<'a, u32>, &'a mut Sum10)>) {
    proof_assert!(invariant::inv(x));
}
