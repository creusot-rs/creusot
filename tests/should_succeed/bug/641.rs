extern crate creusot_contracts;

use creusot_contracts::{law, maintains, open, predicate};

#[law]
#[open]
pub fn test_law() {}

#[open]
#[predicate]
pub fn test() -> bool {
    true
}

#[maintains(test())]
pub fn test_maintains() {}
