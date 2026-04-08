#![feature(unboxed_closures, fn_traits, tuple_trait)]
extern crate creusot_std;
use creusot_std::prelude::*;
use std::marker::Tuple;

#[requires(|mode| f.precondition(a, mode))]
#[ensures(|result, mode| f.postcondition(a, result, mode))]
pub fn weaken_std<A: Tuple, F: Fn<A>>(f: F, a: A) -> F::Output {
    weaken_2_std(f, a)
}

#[requires(|mode| f.precondition(a, mode))]
#[ensures(|result, mode| exists<f2: F> f.postcondition_mut(a, f2, result, mode) && resolve(f2))]
fn weaken_2_std<A: Tuple, F: FnMut<A>>(f: F, a: A) -> F::Output {
    weaken_3_std(f, a)
}

#[requires(|mode| f.precondition(a, mode))]
#[ensures(|result, mode| f.postcondition_once(a, result, mode))]
fn weaken_3_std<A: Tuple, F: FnOnce<A>>(f: F, a: A) -> F::Output {
    FnOnce::call_once(f, a)
}

// Tests that we can actually call a closure, in particular that resolve is correctly compiled
#[requires(|mode| f.precondition((0usize,), mode))]
pub fn fn_once_user<F: FnOnce(usize)>(f: F) {
    f(0)
}

pub fn caller() {
    fn_once_user(|_| ())
}
