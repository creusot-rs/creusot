extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;
#[logic]
#[open]
pub fn my_eq<X: SnapEq>(x: X, y: X) -> bool {
    x == y
}

#[ensures(my_eq(b, result))]
fn test(b: Box<u32>) -> Box<u32> {
    b
}
