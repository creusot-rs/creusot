extern crate creusot_contracts;

use creusot_contracts::*;

pub struct UsesArray([i64; 5]);

#[requires((x.0@).len() > 0 && (x.0@).len() < usize::MAX@)]
pub fn omg(mut x: UsesArray) {
    x.0[0] = 5;

    proof_assert! { @(x.0@)[0] == 5};
}

pub fn call_omg() {
    let arr = [3_i64; 5];
    omg(UsesArray(arr))
}
