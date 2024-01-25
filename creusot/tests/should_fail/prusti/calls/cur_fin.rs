extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('now)]
#[ensures(result == *x)]
fn cur<'a, X: SnapEq>(x: &'a mut X) -> X {
    *x
}

#[logic('x)]
#[ensures(result == *x)]
fn fin<'now, X: SnapEq>(x: &'now mut X) -> X {
    cur(x)
}
