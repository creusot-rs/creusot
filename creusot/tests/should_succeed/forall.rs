extern crate creusot_contracts;

use creusot_contracts::*;

#[ensures(forall<_x:u32> true && true && true && true && true && true && true && true && true)]
pub fn f() {}

#[predicate]
#[requires(a <= b)]
#[ensures(true)]
fn omg(a: Int, b: Int) -> bool {
    pearlite! { {
        exists<c : Int> a + c == b
    } }
}
