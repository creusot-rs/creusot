extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic(('_) -> 'x)]
fn test<X>(x: X) -> X {
    x
}
