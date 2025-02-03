// Test that we can build verified code without enabling unstable features

use creusot_contracts::*;

// Test that `ensures` removes loop invariants
#[ensures(true)]
pub fn f() {
    #[invariant(true)]
    for _ in 0..1 {
        #[creusot_contracts::invariant(true)]
        while false {
            #[::creusot_contracts::invariant(true)]
            loop {}
        }
    }
}
