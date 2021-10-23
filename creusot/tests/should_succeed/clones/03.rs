// SHOULD_SUCCEED: parse-print
extern crate creusot_contracts;

use creusot_contracts::*;

#[logic]
fn omg<T>(x: T) -> bool {
    true
}

#[ensures(omg(x))]
fn prog<T>(x: T) {}

#[ensures(omg(0))]
fn prog2() {
    prog(0);
}

#[ensures(omg((0, 0)))]
fn prog3() {}
