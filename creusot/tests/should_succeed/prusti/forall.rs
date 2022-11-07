extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('_) -> '_)]
pub fn check_bool(_: bool) -> bool {
    true
}

#[requires(forall<b1: bool, b2: bool> check_bool(b1) && check_bool(b2))]
pub fn take_first_mut() {}
