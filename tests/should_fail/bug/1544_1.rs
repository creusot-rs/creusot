extern crate creusot_contracts;
use creusot_contracts::{logic::ops::AddLogic, prelude::*};

pub fn should_not_ice() {
    let x: S<42> = S;
    let _ = snapshot!(x + x);
}

struct S<const X: usize>;
impl<const X: usize> AddLogic for S<X> {
    // Missing the actual items! Caused an ICE in the termination check
}

pub struct BaseCurrency<I, const D: usize>([I; D]);

// Caused an ICE when computing the specialization graph
impl<I, const D: usize> PartialEq for BaseCurrency<I, D> {}
