extern crate creusot_std;
use creusot_std::prelude::*;
use std::ops::{Deref, DerefMut};

#[requires(T::deref.precondition((x,)))]
#[ensures(T::deref.postcondition((x,), result))]
pub fn deref_wrap<T: Deref>(x: &T) -> &T::Target {
    &*x
}

// FIXME: because final reborrow do not work perfectly yet, we cannot prove the function
// using this precondition (we do not know yet that the final value passed to
// deref_mut is equal to that of x):
//#[requires(T::deref_mut.precondition((x,)))]
#[requires(forall<y: &mut T> *y == *x ==> T::deref_mut.precondition((y,)))]
#[ensures(T::deref_mut.postcondition((x,), result))]
pub fn deref_mut_wrap<T: DerefMut>(x: &mut T) -> &mut T::Target {
    &mut *x
}
