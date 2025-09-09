extern crate creusot_contracts;
use creusot_contracts::*;

pub fn foo(x: i32) -> i32 {
    x
}

pub fn baz<const N: i32>() -> i32 {
    N
}

pub fn bar(x: i32) -> i32 {
    let a = foo(x);
    let b = foo(x);
    let c = baz::<42>();
    a + b + c + 42
}

#[refines(foo)]
pub fn foo2(x: i32) -> i32 {
    x
}

#[refines(bar)]
pub fn bar2(x: i32) -> i32 {
    let a = foo(x);
    let b = foo2(x);
    let c = baz::<42>();
    a + b + c + 42
}
