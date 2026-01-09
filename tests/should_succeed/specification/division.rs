extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x != 0u32)]
pub fn divide(y: u32, x: u32) -> u32 {
    y / x
}
