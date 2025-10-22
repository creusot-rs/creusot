// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn unsound() {
    let mut x: Snapshot<bool> = snapshot! { true };
    //            id(xm)   = i1
    let xm: &mut Snapshot<bool> = &mut x;
    // Not final: id(b)    = i2
    let b: &mut Snapshot<bool> = &mut *xm;
    let bg: Snapshot<&mut Snapshot<bool>> = snapshot! { b };
    proof_assert! { ***bg == true && *^*bg == true };
    // Final:     id(evil) = i1
    let evil: &mut Snapshot<bool> = &mut *xm;
    // This proof_assert does not pass !
    // Indeed evil != *bg (because the id do not match), which causes the next line to put `true` inside `*evil`.
    // And thus *^evil == true, disproving the assertion.
    proof_assert! { (evil == *bg) == (*^evil == true) };
    *evil = snapshot! { if evil == *bg { false } else { true } };
    proof_assert! { **evil == !*^evil };
    proof_assert! { **evil == !**evil };
}
