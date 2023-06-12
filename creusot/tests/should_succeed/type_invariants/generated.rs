extern crate creusot_contracts;
use creusot_contracts::{invariant, *};

pub struct List<T>(T, Option<Box<List<T>>>);

pub fn use_list(l: List<i32>) {
    proof_assert!(invariant::inv(l))
}
