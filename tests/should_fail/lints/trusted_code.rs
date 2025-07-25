#![deny(creusot::trusted_code)]

extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
#[ensures(result == 1i32)]
fn foo() -> i32 {
    1i32
}

#[trusted]
pub struct S;

#[logic]
#[ensures(result == (x == 2i32))]
#[trusted]
pub fn is_two(x: i32) -> bool {
    x == 2i32
}

#[allow(creusot::trusted_code)]
#[trusted] // Should not get flagged
#[ensures(is_two(result))]
pub fn bar() -> i32 {
    foo() + 1
}
