#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

struct S1;
struct S2;

impl S1 {
    #[logic]
    fn is_zero_logic(v: i64) -> bool {
        v == 0i64
    }
}

impl S2 {
    #[logic_alias(S1::is_zero_logic(v))]
    fn is_zero_prog(v: i64) -> bool {
        v == 0
    }
}
