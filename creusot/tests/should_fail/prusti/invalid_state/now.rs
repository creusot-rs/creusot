extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(true)]
fn test<'now>(x: u32) -> u32 {
    x
}
