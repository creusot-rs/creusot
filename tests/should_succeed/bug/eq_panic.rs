extern crate creusot_std;
use creusot_std::prelude::*;

// Verifies that the inherited spec for PartialEq can actually be used

pub fn omg<T: Eq + DeepModel>(x: &T, y: &T) -> bool {
    x == y
}
