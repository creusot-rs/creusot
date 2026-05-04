extern crate creusot_std;

use creusot_std::prelude::{vec, *};

pub fn check_iter() {
    let numbers = vec![1, 2, 3, 4, 5, 6];
    let mut iter = numbers.iter();
    let a = iter.next_back().unwrap();
    proof_assert!(a@ == 6);
    let a = iter.next().unwrap();
    proof_assert!(a@ == 1);
    proof_assert!(iter@@ == seq![2i32, 3i32, 4i32, 5i32]);
    let a = iter.next_back().unwrap();
    proof_assert!(a@ == 5);
    let a = iter.next().unwrap();
    proof_assert!(a@ == 2);
    let a = iter.next_back().unwrap();
    proof_assert!(a@ == 4);
    let a = iter.next().unwrap();
    proof_assert!(a@ == 3);
}

pub fn check_iter_mut() {
    let mut numbers = vec![1, 2, 3, 4, 5, 6];
    let mut iter = numbers.iter_mut();
    let a = iter.next_back().unwrap();
    proof_assert!(a@ == 6);
    let a = iter.next().unwrap();
    proof_assert!(a@ == 1);
    let a = iter.next_back().unwrap();
    proof_assert!(a@ == 5);
    let a = iter.next().unwrap();
    proof_assert!(a@ == 2);
}
