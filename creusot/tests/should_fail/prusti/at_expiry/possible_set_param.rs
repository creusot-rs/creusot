extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('x)]
#[ensures(result == at_expiry::<'a>(*x))]
fn test<'a>(x: &'a mut u32) -> u32 {
    at_expiry::<'a>(*x)
}