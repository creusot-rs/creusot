extern crate creusot_contracts;
use creusot_contracts::prelude::*;

pub fn f<T: ?Sized>(p: *const T) {
    proof_assert!(p == (p as *mut T) as *const T)
}

#[ensures(result == p as *const T)]
pub fn thin<T>(p: *const [T]) -> *const T {
    p as *const T
}
