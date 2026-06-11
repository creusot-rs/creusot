extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == x as u8)]
pub fn cast(x: u32) -> u8 {
    x as u8
}
