extern crate creusot_contracts;
use creusot_contracts::*;

pub fn f() {
    let mut x = 12;
    let b = Box::new(&mut x);
    **b += 1;
    proof_assert!(x@ == 13);
    // b is dropped here, but resolved earlier
}
