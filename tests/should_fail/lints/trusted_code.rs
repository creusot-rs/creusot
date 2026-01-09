#![deny(creusot::trusted_code)]

extern crate creusot_std;
use creusot_std::prelude::*;

#[trusted]
#[ensures(result == 1i32)]
fn foo() -> i32 {
    1i32
}

#[trusted]
#[logic]
#[ensures(result == (x == 2i32))]
pub fn is_two(x: i32) -> bool {
    x == 2i32
}

#[allow(creusot::trusted_code)]
#[trusted] // Should not get flagged
#[ensures(is_two(result))]
pub fn bar() -> i32 {
    foo() + 1
}
