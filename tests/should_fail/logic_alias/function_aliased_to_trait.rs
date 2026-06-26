#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

trait T {
    #[logic]
    fn is_zero(x: Int) -> bool {
        x == 0
    }
}

struct S;
impl T for S {}

#[logic_alias(S::is_zero(x@))]
fn is_zero(x: i64) -> bool {
    x == 0
}
