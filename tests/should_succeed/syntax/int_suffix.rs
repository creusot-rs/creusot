extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(*result == 1int)]
pub fn foo() -> Ghost<Int> {
    ghost!(1int)
}
