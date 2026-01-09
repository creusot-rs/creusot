extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn test_law() {}

#[logic(open)]
pub fn test() -> bool {
    true
}

#[maintains(test())]
pub fn test_maintains() {}
