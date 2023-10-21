extern crate creusot_contracts;
use creusot_contracts::*;

pub fn use_borrowed() {
    let mut x = gh! { true };
    let r = &mut x; // x = ?, r = (gh true, x)
    *r = gh! { !x.inner() }; // r = (gh (not (inner x)), x)
                             // resolve r: x = gh (not (inner x))
    proof_assert! { x.inner() == !x.inner() } // UNSOUND!
}
