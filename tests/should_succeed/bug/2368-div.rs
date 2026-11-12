extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == i8::MAX)]
pub fn saturating_div_min() -> i8 {
    i8::MIN.saturating_div(-1)
}
