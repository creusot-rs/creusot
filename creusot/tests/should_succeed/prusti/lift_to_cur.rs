#![warn(creusot::prusti_final)]
extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
fn deref(x: &Box<u32>) -> u32 {
    **x
}

#[open]
#[logic('x)]
pub fn in_logic2<'x, 'now, T>(x: &'now u32) -> &'now u32 {
    x
}

#[ensures(result == deref(x))]
pub fn test(x: &Box<u32>) -> u32 {
    **x
}

pub trait MkRef {
    #[open]
    #[logic]
    fn mk_ref(&self) -> &Self {
        self
    }
}

impl<T> MkRef for T {}

#[ensures({let x = x.mk_ref(); x.0 == result})]
pub fn mk_ref<'a>(x: (u32, u32)) -> u32 {
    x.0
}
