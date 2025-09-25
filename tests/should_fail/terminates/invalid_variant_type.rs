extern crate creusot_contracts;
use creusot_contracts::*;

struct S;

pub fn foo() {
    let x = S;
    #[variant(x)]
    while true {}
}
