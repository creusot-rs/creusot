extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn get_greater_logic(a: Int, b: Int) -> Int {
    if a > b { a } else { b }
}

#[logic_alias(get_greater_logic(x@, y@))]
pub fn is_greater(x: i64, y: i64) -> bool {
    x > y
}
