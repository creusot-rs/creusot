#![feature(min_specialization)]
extern crate creusot_contracts;

use creusot_contracts::*;

#[derive(Resolve)]
pub struct Pair<T, U>(pub T, pub U);
