extern crate creusot_std;

use creusot_std::prelude::{vec, *};

pub fn is_empty() {
    let numbers = vec![1, 2, 3, 4];
    let slice1 = &numbers[0..0];
    let a = slice1.is_empty();
    proof_assert!(a == true);
    let slice2 = &numbers[0..2];
    let b = slice2.is_empty();
    proof_assert!(b == false);
}
