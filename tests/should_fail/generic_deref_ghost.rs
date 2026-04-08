// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::Deref;

#[requires(|mode| T::deref.precondition((x,), mode))]
#[ensures(|result, mode| T::deref.postcondition((x,), result, mode))]
pub fn deref_wrap<T: Deref>(x: &T) -> &T::Target {
    &*x
}

pub fn bad(x: Ghost<i32>) -> i32 {
    *deref_wrap(&x)
}
