// WHY3PROVE
extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
#[requires(false)]
#[variant(x)]
pub fn evil(x: Int) -> Int {
    evil(-x) + 1
}

#[logic]
#[ensures(false)]
pub fn wrong() {
    proof_assert! {evil(1) == evil(-1) + 1};
    proof_assert! {evil(-1) == evil(1) + 1}
}
