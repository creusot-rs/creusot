extern crate creusot_contracts;

use creusot_contracts::{logic, maintains, open};

#[logic(law)]
#[open]
pub fn test_law() {}

#[open]
#[logic]
pub fn test() -> bool {
    true
}

#[maintains(test())]
pub fn test_maintains() {}
