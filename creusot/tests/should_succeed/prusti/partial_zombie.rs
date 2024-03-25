#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(*f0(x) == f1(x))]
pub fn test_tuple(x: (&mut u32, u32)) {
    *x.0 = x.1
}

#[logic]
fn f0<X, Y>(t: (X, Y)) -> X {
    t.0
}

#[logic]
fn f1<X, Y>(t: (X, Y)) -> Y {
    t.1
}
