extern crate creusot_contracts;
use creusot_contracts::*;

pub fn foo(x: i32) -> i32 {
    x
}

pub fn bar(x: i32) -> i32 {
    let y = foo(x);
    y
}

#[refines(foo)]
pub fn foo2(x: i32) -> i32 {
    x
}

#[refines(bar)]
pub fn bar2(x: i32) -> i32 {
    let y = foo2(x);
    y
}
