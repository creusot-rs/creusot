extern crate creusot_contracts;
use creusot_contracts::*;

#[trusted]
pub fn foo(x: i32) -> i32 {
    x
}

#[refines(foo)]
pub fn foo2(x: i32) -> i32 {
    x
}