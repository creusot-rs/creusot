// Test that we can build verified code without enabling unstable features

use creusot_std::prelude::*;

// Test that `ensures` removes loop invariants
#[ensures(true)]
pub fn f() {
    #[invariant(true)]
    for _ in 0..1 {
        #[creusot_std::invariant(true)]
        while false {
            #[::creusot_std::invariant(true)]
            loop {}
        }
    }
}
