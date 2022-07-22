extern crate creusot_contracts;
use creusot_contracts::*;

// Verifies that the inherited spec for PartialEq can actually be used

pub fn omg<T: Eq + Model>(x: &T, y: &T) -> bool {
    x == y
}
