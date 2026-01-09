extern crate creusot_std;

use creusot_std::prelude::*;

// Here we want to ensure that `program` properly shares
// the implementation of simple between itself and `uses_simple`.

#[logic]
pub fn simple() -> bool {
    true
}

#[logic]
pub fn uses_simple() -> bool {
    simple()
}

#[requires(uses_simple())]
#[ensures(simple())]
pub fn program() {}
