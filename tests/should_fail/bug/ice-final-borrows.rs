extern crate creusot_contracts;
use creusot_contracts::prelude::*;

// At some point, mutating an immutable borrow caused the code testing for final borrows
// to crash. This test ensures that it does not happen again.

#[requires(true)]
pub fn mutates_immutable(x: &i32) {
    *x = 1;
}
