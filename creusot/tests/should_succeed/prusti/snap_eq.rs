extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
fn my_eq<X: SnapEq>(x: X, y: X) -> bool {
    x == y
}

#[ensures(my_eq(x, x))]
fn test(x: u32) {}

#[ensures(my_eq(x, x))]
fn test2(x: u32) {}
