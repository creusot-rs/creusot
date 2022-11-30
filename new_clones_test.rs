extern crate creusot_contracts;

use creusot_contracts::*;

#[predicate]
fn omg() -> bool {
    true
}

#[predicate]
fn call_function() -> bool {
    omg()
}

fn omgomg() {
    1 + 1;
}
