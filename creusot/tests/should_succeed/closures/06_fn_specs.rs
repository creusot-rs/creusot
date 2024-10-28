#![feature(unboxed_closures, fn_traits, tuple_trait)]
extern crate creusot_contracts;
use creusot_contracts::{std::ops::*, *};
use std::marker::Tuple;

#[requires(f.precondition(a))]
#[ensures(f.postcondition(a, result))]
pub fn weaken<A: Tuple, F: FnExt<A>>(f: F, a: A) -> F::Output {
    weaken_2(f, a)
}

#[requires(f.precondition(a))]
#[ensures(f.postcondition(a, result))]
pub fn weaken_std<A: Tuple, F: Fn<A>>(f: F, a: A) -> F::Output {
    weaken_2_std(f, a)
}

#[requires(f.precondition(a))]
#[ensures(exists<f2: &mut F> *f2 == f && f2.postcondition_mut(a, result) && resolve(&^f2))]
fn weaken_2<A: Tuple, F: FnMutExt<A>>(f: F, a: A) -> F::Output {
    weaken_3(f, a)
}

#[requires(f.precondition(a))]
#[ensures(exists<f2: &mut F> *f2 == f && f2.postcondition_mut(a, result) && resolve(&^f2))]
fn weaken_2_std<A: Tuple, F: FnMut<A>>(f: F, a: A) -> F::Output {
    weaken_3_std(f, a)
}

#[requires(f.precondition(a))]
#[ensures(f.postcondition_once(a, result))]
fn weaken_3<A: Tuple, F: FnOnceExt<A>>(f: F, a: A) -> F::Output {
    FnOnce::call_once(f, a)
}

#[requires(f.precondition(a))]
#[ensures(f.postcondition_once(a, result))]
fn weaken_3_std<A: Tuple, F: FnOnce<A>>(f: F, a: A) -> F::Output {
    FnOnce::call_once(f, a)
}

// Tests that we can actually call a closure, in particular that resolve is correctly compiled
#[requires(f.precondition((0usize,)))]
pub fn fn_once_user<F: FnOnce(usize)>(f: F) {
    f(0)
}

pub fn caller() {
    fn_once_user(|_| ())
}
