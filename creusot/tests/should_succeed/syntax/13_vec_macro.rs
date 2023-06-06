extern crate creusot_contracts;

use creusot_contracts::{vec, *};

pub fn x() {
    let v0: Vec<u32> = vec![];
    proof_assert! { v0@.len() == 0 };

    let v1 = vec![0; 2];
    proof_assert! { v1@.len() == 2 };

    let v2 = vec![1, 2, 3];
    proof_assert! { v2@.len() == 3 };
}
