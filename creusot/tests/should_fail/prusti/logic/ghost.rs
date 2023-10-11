extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ghost('x)]
fn fin<'curr, 'x, X>(x: &'curr mut X) -> X {
   *x
}