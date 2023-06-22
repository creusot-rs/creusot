extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[open]
#[logic(('curr) -> 'a)]
fn fin<'a, T>(x: &'a mut T) -> T {
    at_expiry::<'a, _>(*x)
}

#[deny(creusot::prusti_zombie)]
#[ensures(fin(result) == *result)]
pub fn zombie_call<'a, T>(x: &'a mut T) -> &'a mut T {
    x
}