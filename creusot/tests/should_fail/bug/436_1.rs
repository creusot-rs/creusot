extern crate creusot_contracts;
use creusot_contracts::*;

struct S {
    g: Ghost<bool>,
}

#[predicate]
fn prophecy(x: &mut S) -> bool {
    pearlite! { *(^x).g }
}

pub fn f() {
    let b = &mut S { g: ghost! { true } };
    b.g = ghost! { !prophecy(b) };
    proof_assert! { false }
}
