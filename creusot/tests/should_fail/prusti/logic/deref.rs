extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('_) -> 'x)]
fn test<'a, X>(x: &'a mut X) -> X {
    *x
}
