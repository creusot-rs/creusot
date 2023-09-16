extern crate creusot_contracts;
use creusot_contracts::*;

#[open]
#[ghost]
pub fn bool_to_bool(b: bool) -> bool {
    b
}

#[open]
#[ghost]
pub fn ex() {
    pearlite! { bool_to_bool(!true) };
}
