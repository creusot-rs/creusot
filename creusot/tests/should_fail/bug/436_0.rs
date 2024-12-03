extern crate creusot_contracts;
use creusot_contracts::*;

struct S {
    g: Snapshot<Int>,
}

#[logic(prophetic)]
fn prophecy(x: &mut S) -> Int {
    pearlite! { *(^x).g }
}

pub fn f() {
    let b = &mut S { g: snapshot! { 1 } };
    b.g = snapshot! { prophecy(b) + 1 };
    proof_assert! { false }
}
