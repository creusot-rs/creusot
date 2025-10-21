extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn negative_is_negative() {
    proof_assert!(0 > -100);
}
