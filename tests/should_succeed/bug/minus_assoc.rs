extern crate creusot_contracts;

use creusot_contracts::prelude::*;

#[ensures(0 - (1 - 1) == 0)]
pub fn f() {}
