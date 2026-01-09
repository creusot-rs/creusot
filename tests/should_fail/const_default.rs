// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

// Check that we don't accidentally use the default value.
pub trait Nat {
    const VALUE: usize = 0;
}

pub fn nat<N: Nat>() {
    // Should fail
    proof_assert! { N::VALUE == 0usize }
}
