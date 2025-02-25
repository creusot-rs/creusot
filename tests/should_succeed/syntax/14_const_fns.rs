extern crate creusot_contracts;
use creusot_contracts::*;

#[requires(x@ == 3)]
pub const fn omg(x: i32) -> i32 {
    x - 1
}
