extern crate creusot_contracts;

use creusot_contracts::*;

#[requires(@i < (@a).len())]
pub fn read_write<T: Eq + Copy + DeepModel>(a: &mut Vec<T>, i: usize, x: T) {
    a[i] = x; // a is slice
    assert!(a[i] == x);
}
