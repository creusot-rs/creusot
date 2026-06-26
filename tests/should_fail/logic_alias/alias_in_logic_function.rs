extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
#[logic_alias(greater(a, b))]
pub fn greater_than(a: i64, b: i64) -> bool {
    a > b
}

pub fn greater(a: i64, b: i64) -> bool {
    a > b
}
