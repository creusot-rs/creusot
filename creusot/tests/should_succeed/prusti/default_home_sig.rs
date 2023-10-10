#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic]
pub fn deref<'a, T>(x: Box<&'a T>) -> &'a T {
    *x
}

// #[open]
// #[predicate]
// pub fn deref_bool<'a, T>(x: Box<&'a bool>) -> bool {**x}