extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[ensures(result == *x)]
fn need_static<X: SnapEq>(x: &'static X) -> X {
    *x
}

#[logic]
#[ensures(result == *x)]
fn cur<'a, X: SnapEq>(x: &'a X) -> X {
    need_static(x)
}
