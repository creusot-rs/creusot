extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic('now)]
pub fn deref<'a>(x: &'a u32) -> u32 {
    *x
}

#[ensures(old(deref(result)) == old(deref(x)))]
pub fn send_back<'a>(x: &'a u32) -> &'a u32 {
    x
}
