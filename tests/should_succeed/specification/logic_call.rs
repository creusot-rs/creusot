extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn reflexive<T: PartialEq>(x: T) -> bool {
    pearlite! { x == x }
}

#[ensures(reflexive(result))]
pub fn dummy() -> u32 {
    0
}
