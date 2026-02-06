extern crate creusot_std;

use creusot_std::prelude::*;

pub fn assertion<T>(x: T) {
    proof_assert! { x == x };
}

#[ensures(b)]
pub fn assume(b: bool) {
    #[trusted]
    proof_assert! { b };
}
