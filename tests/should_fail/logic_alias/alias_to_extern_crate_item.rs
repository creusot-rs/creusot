extern crate creusot_std;

use creusot_std::prelude::*;

#[logic_alias(Int::lt(&x@, &y@))]
pub fn lt(x: i64, y: i64) -> bool {
    x < y
}
