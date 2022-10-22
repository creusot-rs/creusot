extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[logic(('x) -> 'x)]
#[after_expiry(*x == *result)]
fn test<'a, X>(x: &'a mut X) -> &'a mut X {
    x
}
