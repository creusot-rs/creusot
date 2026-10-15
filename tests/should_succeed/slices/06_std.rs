extern crate creusot_std;
use creusot_std::prelude::*;

pub fn split_at_checked() {
    let numbers = [1, 2, 3, 4];
    let split = numbers.split_at_checked(2);
    let expected_l = [1, 2];
    let expected_r = [3, 4];
    proof_assert!(
    match split {
      Some((l, r)) => l@ == expected_l@ && r@ == expected_r@,
      None => false
    });
    let split = numbers.split_at_checked(5);
    proof_assert!(split == None);
}

pub fn split_at_mut_checked() {
    let mut numbers = [1, 2, 3, 4];
    let split = numbers.split_at_mut_checked(2);
    let expected_l = [1, 2];
    let expected_r = [3, 4];
    proof_assert!(
    match split {
      Some((l, r)) => l@ == expected_l@ && r@ == expected_r@,
      None => false
    });
    let split = numbers.split_at_mut_checked(5);
    proof_assert!(split == None);
}
