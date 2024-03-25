extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('now)]
#[ensures(result == **x)]
fn cur<'a, X>(x: &'a mut &'a X) -> X {
    fin2(x)
}

#[logic('x)]
#[ensures(result == **x)]
fn fin2<'now, 'a, X>(x: &'now mut &'a X) -> X {
    **x
}
