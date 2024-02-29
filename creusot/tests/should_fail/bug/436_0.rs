extern crate creusot_contracts;
use creusot_contracts::*;

struct S {
    g: Snapshot<i32>,
}

#[logic(prophetic)]
fn prophecy(x: &mut S) -> i32 {
    pearlite! { *(^x).g }
}

pub fn f() {
    let b = &mut S { g: snapshot! { 1i32 } };
    b.g = snapshot! { prophecy(b) + 1i32 };
    proof_assert! { false }
}
