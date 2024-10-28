extern crate creusot_contracts;
use creusot_contracts::*;

#[deny(creusot::contractless_external_function)]
#[requires(true)]
pub fn f() {
    // We will probably never specify `transmute`, so it is a good target to showcase this lint
    let _x: i32 = unsafe { std::mem::transmute(1i32) };
}
