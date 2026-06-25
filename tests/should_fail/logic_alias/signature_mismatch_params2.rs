extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn is_greater_logic(a: Int, b: Int) -> bool {
    a > b
}

#[logic_alias(is_greater_logic(x@, y))]
pub fn is_greater(x: i64, y: i64) -> bool {
    x > y
}
