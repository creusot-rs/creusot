extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(#[trigger(x)] bad_attr)]
pub fn bad_attr_trigger() {}
