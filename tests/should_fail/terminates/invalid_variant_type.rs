extern crate creusot_std;
use creusot_std::prelude::*;

struct S;

pub fn foo() {
    let x = S;
    #[variant(x)]
    while true {}
}
