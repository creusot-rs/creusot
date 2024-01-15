#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(match Some(x) {None => false, Some(_) => true,})]
pub fn test_op(x: Box<u32>) {}

#[logic]
fn id<X>(x: X) -> X {
    x
}

#[ensures(*id(x) == 5u32)]
pub fn test_id(x: &mut u32) {
    *x = 5
}

#[ensures(*((x, 3).0) == 5u32)]
pub fn test_tuple(x: &mut u32) {
    *x = 5
}
