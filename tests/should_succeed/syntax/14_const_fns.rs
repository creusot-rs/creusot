extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ == 3)]
pub const fn omg(x: i32) -> i32 {
    x - 1
}
