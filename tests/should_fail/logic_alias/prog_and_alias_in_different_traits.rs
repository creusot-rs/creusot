#![allow(unused)]
#![allow(clippy::wrong_self_convention)]

extern crate creusot_std;

use creusot_std::prelude::*;

trait T1 {
    #[logic]
    fn foo_log(self) -> bool;
}

trait T2
where
    Self: T1,
{
    #[logic_alias(Self::foo_log)]
    fn foo_prog(self) -> bool;
}
