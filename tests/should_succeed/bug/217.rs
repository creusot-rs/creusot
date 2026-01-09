extern crate creusot_std;

use creusot_std::{
    logic::{Int, Seq},
    prelude::*,
};

#[logic(open)]
#[variant(c.len())]
pub fn ex(c: Seq<Int>, a: Int) -> Int {
    if c.len() == 0 { 0 } else { ex(c.tail(), a) }
}
