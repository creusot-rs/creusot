extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[check(ghost)]
pub fn faux() -> bool {
    false
}

#[trusted]
#[requires(faux())] // program function called in logic
pub fn f() {}
