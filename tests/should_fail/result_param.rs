extern crate creusot_std;
use creusot_std::prelude::*;

// Should fail saying result is not a valid parameter name
#[ensures(result == result)]
pub fn result_arg(result: u32) {}
