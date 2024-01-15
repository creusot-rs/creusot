extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[logic]
#[open]
pub fn my_eq<X>(x: X, y: X) -> bool {
    x == y
}
