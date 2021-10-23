extern crate creusot_contracts;

use creusot_contracts::*;

// Tests that we can use field access syntax in pearlite.

struct A {
    a: bool,
}

#[trusted]
#[ensures(x.a === x.a)]
pub fn solver(x: A) {}
