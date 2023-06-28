extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic(('curr) -> 'curr)]
pub fn deref<'a, X>(x: &'a X) -> X {
    *x
}

#[ensures(deref(x) == result)]
pub fn test<'a>(x: &'a Box<u32>) -> Box<u32> {
    x.clone()
}