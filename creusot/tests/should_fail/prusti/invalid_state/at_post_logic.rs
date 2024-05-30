extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
fn test(x: u32) -> u32 {
    at_post(x)
}
