extern crate creusot_contracts;
use creusot_contracts::*;

pub fn f<T: ?Sized>(p: *const T) {
    proof_assert!(p == (p as *mut T) as *const T)
}
