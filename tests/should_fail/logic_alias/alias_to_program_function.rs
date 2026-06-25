extern crate creusot_std;

use creusot_std::prelude::*;

pub fn greater_than(a: Int, b: Int) -> bool {
    a > b
}

#[logic_alias(greater_than(a@, b@))]
pub fn greater(a: i64, b: i64) -> bool {
    a > b
}
