extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
#[requires(invariants())]
pub fn emits_pure_eq() -> bool {
    pearlite! {
        (1i32 == 1i32) == true
    }
}

#[logic(open)]
#[requires(invariants())]
#[allow(unused_parens)]
pub fn emits_pure_implies() -> bool {
    pearlite! {
        (1i32 == 1i32) ==> true
    }
}

#[logic]
pub fn invariants() -> bool {
    true
}
