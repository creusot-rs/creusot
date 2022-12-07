extern crate creusot_contracts;

use creusot_contracts::*;

#[logic]
fn a<T>(c: T) -> bool {
    true
}

#[ensures(a(z))]
fn omg<T>(z: T) {}

#[requires(a(0u32))]
fn omg2() {
    omg(0u32);
}
