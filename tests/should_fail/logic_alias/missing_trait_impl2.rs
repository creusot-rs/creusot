#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

struct S1(pub i64);
struct S2;

trait IsZero {
    fn is_zero(&self) -> bool;
}

impl IsZero for S1 {
    #[logic_alias(S2::is_zero_log(self.0))]
    fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl S2 {
    #[logic]
    fn is_zero_log(x: i64) -> bool {
        x == 0i64
    }
}
