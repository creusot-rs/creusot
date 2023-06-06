extern crate creusot_contracts;

use creusot_contracts::{logic::Int, *};

#[ensures(forall<_x:u32> true && true && true && true && true && true && true && true && true)]
pub fn f() {}

#[open]
#[predicate]
#[requires(a <= b)]
#[ensures(true)]
pub fn omg(a: Int, b: Int) -> bool {
    pearlite! { {
        exists<c : Int> a + c == b
    } }
}
