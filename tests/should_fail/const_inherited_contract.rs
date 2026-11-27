// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

// An impl constant inherits the contract of the trait constant: it must be proved, and the
// constant must be opaque at use sites.
pub trait F {
    #[ensures(Self::C@ > 0)]
    const C: i32 = 1;
}

pub struct S;

impl F for S {
    // Should fail: the inherited postcondition does not hold
    const C: i32 = 0;
}

// Should fail: `S::C` is opaque, so its value cannot contradict the inherited postcondition
#[ensures(false)]
pub fn bad() {
    proof_assert!(S::C@ > 0);
}
