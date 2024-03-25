extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic('now, 'y where 'now: 'y)]
fn test<X>(x: Option<X>, default: X) -> X {
    match x {
        Some(x) => x,
        None => default,
    }
}
