extern crate creusot_contracts;

use creusot_contracts::*;

#[requires(x != 0u32)]
pub fn divide(y: u32, x: u32) -> u32 {
    y / x
}
