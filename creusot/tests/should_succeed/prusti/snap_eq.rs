extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
fn my_eq<X: SnapEq>(x: X, y: X) -> bool {
    x == y
}

#[ensures(my_eq(x, x))]
pub fn test(x: u32) {}

#[ensures(old(my_eq(x, x)))]
pub fn test2<X>(x: X) {}
