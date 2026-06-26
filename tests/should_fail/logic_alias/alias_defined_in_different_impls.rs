#![allow(unused)] // to reduce noise in the error message
#![allow(clippy::wrong_self_convention)]

extern crate creusot_std;

use creusot_std::prelude::*;

struct S(i64);

trait T1 {
    #[logic]
    fn is_zero_log(self) -> bool;
}

trait T2 {
    fn is_zero_prog(self) -> bool;
}

impl T1 for S {
    #[logic]
    fn is_zero_log(self) -> bool {
        self.0 == 0i64
    }
}

impl T2 for S {
    #[logic_alias(Self::is_zero_log)]
    fn is_zero_prog(self) -> bool {
        self.0 == 0
    }
}
