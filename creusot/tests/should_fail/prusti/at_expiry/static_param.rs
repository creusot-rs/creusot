extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

#[ensures(at::<'static>(true))]
fn test(x: &'static mut u32) -> &'static mut u32 {
    x
}
