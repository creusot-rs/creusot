extern crate creusot_contracts;

use creusot_contracts::prelude::*;

#[logic]
pub fn reflexive<T: PartialEq>(x: T) -> bool {
    pearlite! { x == x }
}

#[ensures(reflexive(result))]
pub fn dummy() -> u32 {
    0
}
