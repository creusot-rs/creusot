extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[logic(open)]
pub fn test_law() {}

#[logic(open)]
pub fn test() -> bool {
    true
}

#[maintains(test())]
pub fn test_maintains() {}
