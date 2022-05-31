// UNBOUNDED
extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(@result == @4294967294u32)]
pub fn no_bounds_check(_x: i32, _y: i32) -> i32 {
    2_147_483_647 + 2_147_483_647
}

#[logic]
pub fn no_conversion(x: u32) -> Int {
    x.model()
}
