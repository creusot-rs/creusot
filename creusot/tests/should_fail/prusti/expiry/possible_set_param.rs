extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('x)]
#[after_expiry('a, result == *x)]
fn test<'a>(x: &'a mut u32) -> u32 {
    0u32
}