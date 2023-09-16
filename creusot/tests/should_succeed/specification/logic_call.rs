extern crate creusot_contracts;

use creusot_contracts::*;

#[ghost]
fn reflexive<T: PartialEq>(x: T) -> bool {
    pearlite! { x == x }
}

#[ensures(reflexive(result))]
pub fn dummy() -> u32 {
    0
}
