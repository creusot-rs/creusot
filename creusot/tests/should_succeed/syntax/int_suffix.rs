extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(*result == 1int)]
pub fn foo() -> GhostBox<Int> {
    ghost!(1int)
}
