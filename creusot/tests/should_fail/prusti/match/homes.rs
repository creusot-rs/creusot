extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('x, 'y) -> 'x)]
fn test<X>(x: Option<X>, default: X) -> X {
    match x {
        Some(x) => x,
        None => default
    }
}