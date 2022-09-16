extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
#[requires(invariants())]
pub fn emits_pure_eq() -> bool {
    pearlite! {
        (1i32 == 1i32) == true
    }
}

#[logic]
#[requires(invariants())]
pub fn emits_pure_implies() -> bool {
    pearlite! {
        (1i32 == 1i32) ==> true
    }
}

#[logic]
fn invariants() -> bool {
    true
}
