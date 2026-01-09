extern crate creusot_std;
use creusot_std::prelude::*;

pub enum Empty {}

#[requires(match empty { })]
pub fn foo(empty: Empty) {}
