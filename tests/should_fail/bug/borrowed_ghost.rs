extern crate creusot_contracts;
use creusot_contracts::*;

pub fn use_borrowed() {
    let mut x = snapshot! { true };
    let r = &mut x; // x = ?, r = (snapshot true, x)
    *r = snapshot! { !x.inner() }; // r = (snapshot (not (inner x)), x)
    // resolve r: x = snapshot (not (inner x))
    proof_assert! { x.inner() == !x.inner() } // UNSOUND!
}
