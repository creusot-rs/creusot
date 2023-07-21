extern crate creusot_contracts;
use creusot_contracts::*;

struct S {
    g: Ghost<i32>,
}

#[ghost]
fn prophecy(x: &mut S) -> i32 {
    pearlite! { *(^x).g }
}

pub fn f() {
    let b = &mut S { g: gh! { 1i32 } };
    b.g = gh! { prophecy(b) + 1i32 };
    proof_assert! { false }
}
