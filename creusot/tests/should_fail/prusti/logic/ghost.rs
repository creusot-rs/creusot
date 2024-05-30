extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('x)]
fn fin<'now, 'x, X>(x: &'now mut X) -> X {
    *x
}
