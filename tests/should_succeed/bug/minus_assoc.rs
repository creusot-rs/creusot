extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(0 - (1 - 1) == 0)]
pub fn f() {}
