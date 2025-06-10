extern crate creusot_contracts;
use creusot_contracts::*;

pub enum Empty {}

#[requires(match empty { })]
pub fn foo(empty: Empty) {}
