extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(old(b) == result)]
pub fn test(b: Box<u32>) -> Box<u32> {
    b
}
