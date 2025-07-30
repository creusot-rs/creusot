extern crate creusot_contracts;
use creusot_contracts::*;

// Should fail saying result is not a valid parameter name
#[ensures(result == result)]
pub fn result_arg(result: u32) {}
