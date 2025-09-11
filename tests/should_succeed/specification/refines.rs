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

// Test handling of reference arguments (autoref and reborrows)
trait Tr {
    fn takes_ref(&self) -> Self;
}

impl Tr for i32 {
    fn takes_ref(&self) -> Self {
        *self
    }
}

#[refines(<i32 as Tr>::takes_ref)]
fn takes_ref(x: &i32) -> i32 {
    *x
}

pub fn takes_ref_test(x: i32) -> i32 {
    // Autoref makes this `(&x).takes_ref()`
    x.takes_ref()
}

#[refines(takes_ref_test)]
pub fn takes_ref_test2(x: i32) -> i32 {
    // THIR introduces a reborrow, making this `takes_ref(&*&x)`
    takes_ref(&x)
}

#[refines(foo)]
fn foog(x: i32) -> (i32, Ghost<i32>) {
    (x, ghost!(x))
}
