extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('curr)]
#[ensures(result == *x)]
fn cur<'a, X>(x: &'a mut X) -> X {
    *x
}

#[logic('x)]
#[ensures(result == *x)]
fn fin<'curr, X>(x: &'curr mut X) -> X {
    cur(x)
}