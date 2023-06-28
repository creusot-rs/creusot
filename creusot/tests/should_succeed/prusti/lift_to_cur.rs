extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('curr) -> 'curr)]
fn deref(x: &Box<u32>) -> u32 {
    **x
}

#[open]
#[logic(('curr) -> 'a)]
pub fn in_logic1<'a, T>(x: &'a T) -> &'a T {
    x
}

#[open]
#[logic(('x) -> 'curr)]
pub fn in_logic2<'x, 'curr, T>(x: &'curr u32) -> &'curr u32 {
    x
}

#[ensures(result == deref(x))]
pub fn test(x: &Box<u32>) -> u32 {
    **x
}

pub trait MkRef {
    #[open]
    #[logic(('x) -> 'x)]
    fn mk_ref(&self) -> &Self {
        self
    }
}

impl<T> MkRef for T {}

#[ensures({let x = x.mk_ref(); x.0 == result})]
pub fn mk_ref<'a>(x: (u32, u32)) -> u32 {
    x.0
}