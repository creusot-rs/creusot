extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(true)]
fn test<'pre>(x: &'pre u32) -> u32 {
    *x
}
