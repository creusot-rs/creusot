extern crate creusot_contracts;
use creusot_contracts::prelude::*;

struct S;

pub fn foo() {
    let x = S;
    #[variant(x)]
    while true {}
}
