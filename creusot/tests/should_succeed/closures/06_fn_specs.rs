#![feature(unboxed_closures, fn_traits)]
extern crate creusot_contracts;
use creusot_contracts::{std::*, *};

#[requires(f.precondition(a))]
#[ensures(f.postcondition(a, result))]
pub fn weaken<A, F: FnSpec<A> + Resolve>(f: F, a: A) -> F::Output {
    weaken_2(f, a)
}

#[requires(f.precondition(a))]
#[ensures(exists<f2: &mut F> *f2 == f && f2.postcondition_mut(a, result) && (^f2).resolve())]
fn weaken_2<A, F: FnMutSpec<A> + Resolve>(f: F, a: A) -> F::Output {
    weaken_3(f, a)
}

#[requires(f.precondition(a))]
#[ensures(f.postcondition_once(a, result))]
fn weaken_3<A, F: FnOnceSpec<A> + Resolve>(f: F, a: A) -> F::Output {
    FnOnce::call_once(f, a)
}
