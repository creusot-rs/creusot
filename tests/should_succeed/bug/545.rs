extern crate creusot_std;
use creusot_std::prelude::*;

pub fn negative_is_negative() {
    proof_assert!(0 > -100);
}
