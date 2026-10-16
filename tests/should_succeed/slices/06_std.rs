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

pub fn split_first() {
    let numbers = [1, 2, 3, 4];
    let split = numbers.split_first();
    let rest = [2, 3, 4];
    proof_assert!(
    match split {
      Some((h, r)) => h@ == 1 && r@ == rest@,
      None => false
    });
}

pub fn split_last_1() {
    let numbers = [1, 2, 3, 4];
    let split = numbers.split_last();
    let rest = [1, 2, 3];
    proof_assert!(
    match split {
      Some((t, r)) => t@ == 4 && r@ == rest@,
      None => false
    });
}

pub fn split_last_2() {
    let numbers: [i32; 0] = [];
    let split = numbers.split_last();
    proof_assert!(split == None);
}

pub fn split_last_mut_1() {
    let mut numbers = [1, 2, 3, 4];
    let split = numbers.split_last_mut();
    let rest = [1, 2, 3];
    proof_assert!(
    match split {
      Some((t, r)) => t@ == 4 && r@ == rest@,
      None => false
    });
}

pub fn split_last_mut_2() {
    let mut numbers: [i32; 0] = [];
    let split = numbers.split_last_mut();
    proof_assert!(split == None);
}
