extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[variant(x)]
#[requires(x >= 0)]
#[ensures(result == x)]
pub fn variant_int(x: Int) -> Int {
    if x == 0 { 0 } else { 1 + variant_int(x - 1) }
}
