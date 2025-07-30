extern crate creusot_contracts;
use creusot_contracts::*;

struct S {
    g: Snapshot<bool>,
}

#[logic]
fn prophecy(x: &mut S) -> bool {
    pearlite! { *(^x).g }
}

pub fn f() {
    let b = &mut S { g: snapshot! { true } };
    b.g = snapshot! { !prophecy(b) };
    proof_assert! { false }
}
