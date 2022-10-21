extern crate creusot_contracts;

use creusot_contracts::{law, maintains, predicate};

#[law]
pub fn test_law() {}

#[predicate]
pub fn test() -> bool {
    true
}

#[maintains(test())]
pub fn test_maintains() {}
