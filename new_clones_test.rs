extern crate creusot_contracts;

use creusot_contracts::*;

// #[logic]
// fn b<T>(x: T) -> bool { x == x }

// #[logic]
// fn a<T>(c: T) -> bool { b(c) }

// #[ensures(a(z))]
fn omg<T>(z: T) {}

// #[requires(a(0u32))]
fn omg2() {
    omg(0u32);
}
