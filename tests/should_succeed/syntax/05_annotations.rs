extern crate creusot_std;

use creusot_std::prelude::*;

pub fn assertion<T>(x: T) {
    proof_assert! { x == x };
}
