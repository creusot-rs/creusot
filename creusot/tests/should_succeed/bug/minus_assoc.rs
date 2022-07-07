extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(0 - (1 - 1) == 0)]
pub fn f() {}
