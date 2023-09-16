extern crate creusot_contracts;

use creusot_contracts::{
    logic::{Int, Seq},
    *,
};

#[open]
#[ghost]
#[variant(c.len())]
pub fn ex(c: Seq<Int>, a: Int) -> Int {
    if c.len() == 0 {
        0
    } else {
        ex(c.tail(), a)
    }
}
