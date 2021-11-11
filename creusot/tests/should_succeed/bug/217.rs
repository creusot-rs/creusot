extern crate creusot_contracts;

use creusot_contracts::std::*;
use creusot_contracts::*;

#[logic]
#[variant(c.len())]
fn ex(c: Seq<Int>, a: Int) -> Int {
    if c.len() == 0 {
        0
    } else {
        ex(c.tail(), a)
    }
}
