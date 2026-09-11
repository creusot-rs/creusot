extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(mode!().ghost())]
pub fn f() {}
