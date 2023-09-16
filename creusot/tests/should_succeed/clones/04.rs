extern crate creusot_contracts;

use creusot_contracts::*;

#[ghost]
fn a(x: u32) -> bool {
    x > 0u32
}

#[ghost]
fn b(x: u32) -> bool {
    x > 10u32 && a(x)
}

#[ghost]
fn c(x: u32) -> bool {
    x < 50u32 && b(x)
}

#[requires(c(x))]
pub fn f(x: u32) {}
