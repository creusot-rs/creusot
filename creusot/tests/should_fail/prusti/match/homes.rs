extern crate creusot_contracts;
use creusot_contracts::prusti::*;

#[logic(('x, 'y) -> 'x)]
pub fn test<X>(x: Option<X>, default: X) -> X {
    match x {
        Some(x) => x,
        None => default
    }
}