extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
pub unsafe fn test(x: *mut u32) -> &'static mut u32 {
    &mut *x
}