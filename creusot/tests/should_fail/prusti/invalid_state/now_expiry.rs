extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[after_expiry('now, result == x)]
fn test(x: u32) -> u32 {
    x
}
