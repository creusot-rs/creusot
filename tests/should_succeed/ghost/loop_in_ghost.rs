extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(*result == x)]
pub fn foo(x: u32) -> Ghost<u32> {
    ghost! {
        let mut y = 0;
        let mut i = x;
        #[variant(i)]
        #[invariant(y@ + i@ == x@)]
        while i > 0 {
            i -= 1;
            y += 1;
        }
        y
    }
}
