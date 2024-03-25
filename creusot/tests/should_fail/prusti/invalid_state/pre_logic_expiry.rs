extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[after_expiry('pre, result == x)]
fn test(x: u32) -> u32 {
    x
}
