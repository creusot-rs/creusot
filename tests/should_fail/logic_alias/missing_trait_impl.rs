#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

struct S1(pub i64);
struct S2;

trait IsZeroLog {
    #[logic]
    fn is_zero_logic(self) -> bool;
}

impl IsZeroLog for S1 {
    #[logic]
    fn is_zero_logic(self) -> bool {
        self.0 == 0i64
    }
}

impl S2 {
    #[logic_alias(S1::is_zero_logic(S1(v)))]
    fn is_zero_prog(v: i64) -> bool {
        v == 0
    }
}
