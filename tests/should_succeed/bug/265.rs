extern crate creusot_contracts;
use creusot_contracts::*;

#[open]
#[logic]
pub fn bool_to_bool(b: bool) -> bool {
    b
}

#[open]
#[logic]
pub fn ex() {
    pearlite! { bool_to_bool(!true) };
}
