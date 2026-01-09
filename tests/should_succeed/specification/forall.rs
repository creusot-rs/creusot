extern crate creusot_std;

use creusot_std::{logic::Int, prelude::*};

#[ensures(forall<_x:u32> true && true && true && true && true && true && true && true && true)]
pub fn f() {}

#[logic(open)]
#[requires(a <= b)]
#[ensures(true)]
pub fn omg(a: Int, b: Int) -> bool {
    pearlite! { {
        exists<c> a + c == b
    } }
}
