#![feature(unboxed_closures, fn_traits, tuple_trait)]
extern crate creusot_contracts;
use creusot_contracts::{std::ops::*, *};
use std::marker::Tuple;


#[requires(f.precondition(a))]
#[ensures(f.postcondition_once(a, result))]
fn weaken_3<A: Tuple, F: FnOnceExt<A>>(f: F, a: A) -> F::Output {
    FnOnce::call_once(f, a)
}

// #[requires(f.precondition(a))]
// #[ensures(f.postcondition_once(a, result))]
// fn weaken_3_std<A: Tuple, F: FnOnce<A>>(f: F, a: A) -> F::Output {
//     FnOnce::call_once(f, a)
// }