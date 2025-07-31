extern crate creusot_contracts;

use creusot_contracts::*;

#[logic]
pub fn omg<T>(_x: T) -> bool {
    true
}

#[ensures(omg(x))]
fn prog<T>(x: T) {}

#[ensures(omg(0))]
pub fn prog2() {
    prog(0);
}

#[ensures(omg((0, 0)))]
pub fn prog3() {}
