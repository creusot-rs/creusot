#![feature(min_specialization)]
extern crate creusot_contracts;

use creusot_contracts::*;

#[derive(Resolve)]
struct Pair<T, U>(T, U);
