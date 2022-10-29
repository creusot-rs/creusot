extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[logic(('curr) -> 'curr)]
#[ensures(result == *x)]
pub fn cur<'a, X>(x: &'a mut X) -> X {
    fin(x)
}

#[logic(('x) -> 'curr)]
#[ensures(result == *x)]
pub fn fin<'curr, X>(x: &'curr mut X) -> X {
    *x
}