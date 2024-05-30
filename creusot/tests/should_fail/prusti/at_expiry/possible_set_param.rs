extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('x)]
#[ensures(result == at::<'a>(*x))]
fn test<'a>(x: &'a mut u32) -> u32 {
    at::<'a>(*x)
}
