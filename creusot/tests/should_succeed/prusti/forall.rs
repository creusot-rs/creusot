extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic]
pub fn check_bool(_: bool) -> bool {
    true
}

#[requires(forall<b1: bool, b2: bool> check_bool(b1) && check_bool(b2))]
pub fn test1() {}

pub trait Check {
    #[logic]
    fn check(self) -> bool;
}

#[requires(forall<t: T> t.check())]
pub fn test2<T: Check>() {}
