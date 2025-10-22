extern crate creusot_contracts;
use creusot_contracts::prelude::*;

// Should fail saying result is not a valid parameter name
#[ensures(result == result)]
pub fn result_arg(result: u32) {}
