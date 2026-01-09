extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(result == 1)]
fn f() -> Int {
    1
}

#[logic(open)]
#[ensures(result == 2)]
pub fn g() -> Int {
    proof_assert!(f() == 1);
    let _ = f;
    2
}
