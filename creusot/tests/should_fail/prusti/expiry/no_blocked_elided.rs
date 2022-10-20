extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[after_expiry(true)]
fn test<'a>(x: &'a mut u32, y: &mut u32) -> &'a mut u32 {
    x
}