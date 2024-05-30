extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[ensures(result == old(x))]
fn test(x: u32) -> u32 {
    x
}
