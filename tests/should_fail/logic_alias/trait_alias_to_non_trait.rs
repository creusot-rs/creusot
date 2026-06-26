#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

struct S;

impl S {
    #[logic]
    fn is_zero(x: Int) -> bool {
        x == 0
    }
}

trait T {
    #[logic_alias(S::is_zero(x@))]
    fn is_zero(x: i64) -> bool {
        x == 0
    }
}
