extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(@result == (@slice).len())]
pub fn slice_iter<T>(slice: &[T]) -> usize {
    let mut i = 0;
    for _ in slice {
        i += 1;
    }
    i
}

#[ensures(@result == (@vec).len())]
pub fn vec_iter<T>(vec: &Vec<T>) -> usize {
    let mut i = 0;
    for _ in vec {
        i += 1;
    }
    i
}
