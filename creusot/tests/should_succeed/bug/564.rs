extern crate creusot_contracts;
use creusot_contracts::*;

#[ghost]
#[open]
#[requires(invariants())]
pub fn emits_pure_eq() -> bool {
    pearlite! {
        (1i32 == 1i32) == true
    }
}

#[ghost]
#[open]
#[requires(invariants())]
pub fn emits_pure_implies() -> bool {
    pearlite! {
        (1i32 == 1i32) ==> true
    }
}

#[ghost]
fn invariants() -> bool {
    true
}
