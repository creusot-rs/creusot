extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[after_expiry(*x == *result)]
fn test<'a, X>(x: &'a mut X) -> &'a mut X {
    x
}
