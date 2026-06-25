extern crate creusot_std;

use creusot_std::prelude::*;

#[logic]
pub fn is_odd_logic(a: i64) -> bool {
    a & 1i64 != 0i64
}

#[logic]
pub fn is_even_logic(a: i64) -> bool {
    !is_odd_logic(a)
}

#[logic_alias(is_odd_logic)]
#[logic_alias(is_even_logic)]
pub fn is_odd(x: i64) -> bool {
    x & 1 != 0
}
