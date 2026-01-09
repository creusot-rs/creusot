extern crate creusot_std;
use creusot_std::prelude::*;

// Test handling of shifts by vcgen
#[logic]
#[requires(left@ < 8)]
pub fn nth_bit_from_left_8(x: u8, left: usize) -> bool {
    let mask: u8 = 1u8 << (7usize - left);
    (x & mask) != 0u8
}
