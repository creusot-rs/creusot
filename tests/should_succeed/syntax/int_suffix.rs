extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[ensures(*result == 1int)]
pub fn foo() -> Ghost<Int> {
    ghost!(1int)
}
