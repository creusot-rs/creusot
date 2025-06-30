extern crate creusot_contracts;

use creusot_contracts::{law, logic, maintains, open};

#[law]
#[open]
pub fn test_law() {}

#[open]
#[logic]
pub fn test() -> bool {
    true
}

#[maintains(test())]
pub fn test_maintains() {}
