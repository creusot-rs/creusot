extern crate creusot_contracts;
use creusot_contracts::*;

pub fn unsound() {
    let mut x: Ghost<bool> = gh! { true };
    //            id(xm)   = i1
    let xm: &mut Ghost<bool> = &mut x;
    // Not final: id(b)    = i2
    let b: &mut Ghost<bool> = &mut *xm;
    let bg: Ghost<&mut Ghost<bool>> = gh! { b };
    proof_assert! { ***bg == true && *^*bg == true };
    // Final:     id(evil) = i1
    let evil: &mut Ghost<bool> = &mut *xm;
    // This proof_assert does not pass !
    // Indeed evil != *bg (because the id do not match), which causes the next line to put `true` inside `*evil`.
    // And thus *^evil == true, disproving the assertion.
    proof_assert! { (evil == *bg) == (*^evil == true) };
    *evil = gh! { if evil == *bg { false } else { true } };
    proof_assert! { **evil == !*^evil };
    proof_assert! { **evil == !**evil };
}
