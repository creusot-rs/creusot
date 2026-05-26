extern crate creusot_std;

use creusot_std::prelude::{vec, *};

pub fn check_iter_len() {
    let numbers = vec![1, 2, 3, 4];
    let mut iter = numbers.iter();
    let len = iter.len();
    proof_assert!(len@ == 4);
    iter.next();
    let len = iter.len();
    proof_assert!(len@ == 3);
    iter.next();
    let len = iter.len();
    proof_assert!(len@ == 2);
}

pub fn check_iter_mut_len() {
    let numbers = vec![1, 2, 3, 4];
    let mut iter = numbers.iter();
    let len = iter.len();
    proof_assert!(len@ == 4);
    iter.next();
    let len = iter.len();
    proof_assert!(len@ == 3);
    iter.next();
    let len = iter.len();
    proof_assert!(len@ == 2);
}
