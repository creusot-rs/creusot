extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn get_greater_logic(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}

#[logic_alias(get_greater_logic(a as i64, b as i64).into())]
pub fn get_greater(a: i64, b: i64) -> i64 {
    if a > b { a } else { b }
}
