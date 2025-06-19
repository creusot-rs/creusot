extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result == p as *mut T)]
pub fn f<T: ?Sized>(p: *const T) -> *mut T {
    p as *mut T
}

#[ensures(result == p as *const T)]
pub fn g<T: ?Sized>(p: *mut T) -> *const T {
    p as *const T
}
