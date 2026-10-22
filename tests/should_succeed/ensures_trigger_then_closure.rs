extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[requires(x != 0u32)]
#[requires(x != 1u32)]
#[ensures(
    #[trigger(result)]
    |result @ (a, b)|
    a == b
)]
pub fn pair(x: u32) -> (u32, u32) {
    (x, x)
}

#[logic]
#[requires(x != 0u32)]
#[requires(x != 1u32)]
#[ensures(result.0 == result.1)]
pub fn use_pair(x: u32) -> (u32, u32) {
    pair(x)
}
