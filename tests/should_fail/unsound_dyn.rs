extern crate creusot_std;
use creusot_std::prelude::*;

// - Any `trait Tr` is implemented by `dyn Tr`,
// - but `trait False` below has no valid implementation.
// Contradiction.
//
// We prevent this by restricting the traits allowed in `dyn`.
pub trait False {
    #[logic]
    #[ensures(false)]
    fn falso(&self);
}

#[ensures(false)]
pub fn unsound() {
    proof_assert! { forall<x: dyn False> x.falso() == () }
}
