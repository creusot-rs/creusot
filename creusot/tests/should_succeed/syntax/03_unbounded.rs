// UNBOUNDED
extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(result == 4294967294u32)]
fn no_bounds_check(x: u32, y: u32) -> u32 {
    2_147_483_647 + 2_147_483_647
}

#[logic]
fn no_conversion(x: u32) -> Int {
    x.model()
}
