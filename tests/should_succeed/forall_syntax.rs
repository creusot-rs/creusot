extern crate creusot_std;

use creusot_std::{logic::Int, prelude::*};

#[logic(open)]
#[ensures(result)]
pub fn basic(a: Int) -> bool {
    forall(|c| a + c - c == a)
}

#[logic(open)]
#[ensures(result)]
pub fn multi_arg(a: Int, b: Int) -> bool {
    forall(|c, d| a + c - c == a && a - d + d == a)
}

#[logic(open)]
#[ensures(result)]
pub fn triggers(a: Int, b: Int) -> bool {
    forall(
        #[trigger(a + c, a + d)]
        |c, d| a + c - c == a && a - d + d == a,
    )
}
