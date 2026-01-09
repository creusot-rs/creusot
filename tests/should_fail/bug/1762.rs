extern crate creusot_std;
use creusot_std::prelude::*;

#[check(ghost)]
pub fn faux() -> bool {
    false
}

#[trusted]
#[requires(faux())] // program function called in logic
pub fn f() {}
