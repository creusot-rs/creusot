// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::Deref;

#[requires(|mode| T::deref.precondition(mode, (x,)))]
#[ensures(|result, mode| T::deref.postcondition(mode, (x,), result))]
pub fn deref_wrap<T: Deref>(x: &T) -> &T::Target {
    &*x
}

pub fn bad(x: Snapshot<i32>) -> i32 {
    *deref_wrap(&x)
}
