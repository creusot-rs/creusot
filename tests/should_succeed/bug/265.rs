extern crate creusot_contracts;
use creusot_contracts::prelude::*;

#[logic(open)]
pub fn bool_to_bool(b: bool) -> bool {
    b
}

#[logic(open)]
pub fn ex() {
    pearlite! { bool_to_bool(!true) };
}
