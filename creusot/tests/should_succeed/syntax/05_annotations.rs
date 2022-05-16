extern crate creusot_contracts;

use creusot_contracts::*;

fn assertion<T>(x: T) {
    proof_assert! { x == x };
}
