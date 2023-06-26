extern crate creusot_contracts;
use creusot_contracts::*;

struct S {
    g: Ghost<i32>
}

#[logic]
fn prophecy(x: &mut S) -> i32 {
    pearlite!{ *(^x).g }
}

pub fn f() {
    let b = &mut S{ g:ghost! { 1 } };
    b.g = ghost!{ prophecy(b) + 1 };
    proof_assert! { false }
}
