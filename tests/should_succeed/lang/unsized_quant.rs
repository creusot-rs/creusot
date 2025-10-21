extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[logic]
pub fn f() -> bool {
    pearlite! {
        let len = |x: [i32]| x@.len();
        forall<x: [i32], y: [i32]> {
            len[x] + len[y] >= 0
        }
    }
}

#[logic]
#[ensures(f())]
pub fn l() {}
