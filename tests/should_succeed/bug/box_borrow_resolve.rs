extern crate creusot_contracts;
use creusot_contracts::prelude::*;

// Check that the borrow inside `x` is resolved.
#[ensures(result == *x)]
pub fn borrow_in_box(x: Box<&mut i32>) -> &mut i32 {
    &mut **x
}
