extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ghost('x)]
fn fin<'now, 'x, X>(x: &'now mut X) -> X {
    *x
}
