extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(x == x)]
fn test(x: (&mut u32, u32)) {}
