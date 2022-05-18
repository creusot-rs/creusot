extern crate creusot_contracts;
use creusot_contracts::*;

#[logic]
fn bool_to_bool(b: bool) -> bool {
    b
}

#[logic]
fn ex() {
    pearlite! { bool_to_bool(!true) };
}
