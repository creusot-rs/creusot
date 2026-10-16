extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(clippy::manual_swap)]
#[requires(*<Box<T> as core::ops::Deref>::deref(b1) != *<Box<T> as core::ops::Deref>::deref(b2))]
#[ensures(*<Box<T> as core::ops::Deref>::deref(b1) == *<Box<T> as core::ops::Deref>::deref(&^b2))]
#[ensures(*<Box<T> as core::ops::DerefMut>::deref_mut(b2) == *^b1)]
pub fn dummy_swap<T: Copy>(b1: &mut Box<T>, b2: &mut Box<T>) {
    let tmp = **b1;
    **b1 = **b2;
    **b2 = tmp;
}
