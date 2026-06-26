#![allow(unused)] // to reduce noise in the error message

extern crate creusot_std;

use creusot_std::prelude::*;

trait T1 {
    #[logic]
    fn is_zero_log(x: Int) -> bool;
}

trait T2
where
    Self: T1,
{
    #[logic_alias(Self::is_zero_log(x@))]
    fn is_zero(x: i64) -> bool;
}
