extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

// #[logic(('curr) -> 'curr)]
// fn deref(x: &Box<u32>) -> u32 {
//     **x
// }
//
// #[ensures(result == deref(x))]
// fn test(x: &Box<u32>) -> u32 {
//     **x
// }

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