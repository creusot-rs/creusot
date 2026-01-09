extern crate creusot_std;
use creusot_std::prelude::*;

// Check that the borrow inside `x` is resolved.
#[ensures(result == *x)]
pub fn borrow_in_box(x: Box<&mut i32>) -> &mut i32 {
    &mut **x
}
