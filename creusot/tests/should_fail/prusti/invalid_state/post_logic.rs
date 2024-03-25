extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
fn test<'post>(x: u32) -> u32 {
    x
}
