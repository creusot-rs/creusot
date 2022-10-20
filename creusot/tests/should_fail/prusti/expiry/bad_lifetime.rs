extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[after_expiry('x, true)]
fn test<'a>(_: &'a mut u32, _: &'a u32) {

}