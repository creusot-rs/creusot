extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[after_expiry('post, result == x)]
fn test(x: u32) -> u32 {
    x
}
