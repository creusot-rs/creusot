extern crate creusot_contracts;
use creusot_contracts::*;

// Check that we can make snapshots in ghost code.
pub fn foo() {
    ghost! {
        let x = snapshot!(1);
        proof_assert!(*x == 1);
    };
}

// Check that we can make snapshots in ghost functions.
#[check(ghost)]
pub fn is_ghost() {
    let x = snapshot!(1);
    proof_assert!(*x == 1);
}

// Check that we can make move variable into pearlite functions, without triggering the
// "program variable used in ghost block" check.
pub fn bar() {
    let x = Box::new(1i32);
    ghost! {
        let _ = snapshot!(x);
        proof_assert!(exists<y: i32> **Box::new(x) == y);
    };
}
