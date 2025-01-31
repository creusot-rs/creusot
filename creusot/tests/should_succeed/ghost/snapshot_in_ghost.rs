extern crate creusot_contracts;
use creusot_contracts::*;

// Check that we can make snapshots in ghost code.
pub fn foo() {
    ghost! {
        let x = snapshot!(1);
        proof_assert!(*x == 1);
    };
}

// Check that we can make snapshots in pure functions.
#[pure]
pub fn is_pure() {
    let x = snapshot!(1);
    proof_assert!(*x == 1);
}
