extern crate creusot_contracts;

use creusot_contracts::*;

#[requires(10 < (@a).len())]
pub fn index_slice(a: &[u32]) -> u32 {
    a[10]
}

#[requires((@a).len() == 5)]
#[ensures(@(@^a)[2] == 3)]
pub fn index_mut_slice(a: &mut [u32]) {
    a[2] = 3;
}

#[ensures(match result {
    Some(v) => *v == (@a)[0],
    None => (@a).len() == 0
})]
pub fn slice_first<T>(a: &[T]) -> Option<&T> {
    if a.len() > 0 {
        Some(&a[0])
    } else {
        None
    }
}
