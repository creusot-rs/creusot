extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(i@ < a@.len())]
pub fn read_write<T: Eq + Copy + DeepModel>(a: &mut Vec<T>, i: usize, x: T) {
    a[i] = x; // a is slice
    assert!(a[i] == x);
}
