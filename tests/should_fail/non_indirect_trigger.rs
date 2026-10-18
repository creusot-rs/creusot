extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(#[trigger(x)] open)]
pub fn bad_attr_trigger() {}
