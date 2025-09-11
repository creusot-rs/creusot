extern crate creusot_contracts;
use creusot_contracts::*;

fn foo(x: i32) -> i32 {
    x
}

#[refines(foo)]
fn foo2(x: i32, _: Ghost<Int>) -> i32 {
    x
}

fn baz<const N: i32>() -> i32 {
    N
}

trait Quux {
    fn quux(&self) -> i32;
}

impl Quux for i32 {
    fn quux(&self) -> i32 {
        foo(*self)
    }
}

#[refines(<i32 as Quux>::quux)]
fn quux2(x: &i32, y: Ghost<Int>) -> i32 {
    foo2(*x, y)
}

pub fn test_foo(x: i32) -> i32 {
    let a = foo(x);
    let b = foo(x);
    let c = baz::<42>();
    let c = c.quux();
    a + b + c + 42
}

#[refines(test_foo)]
pub fn test_foo2(x: i32, y: Ghost<Int>) -> i32 {
    let a = foo(x);
    let b = foo2(x, y);
    let c = baz::<42>();
    let c = quux2(&c, y);
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

pub fn test_ghost_fields(x: i32) -> i32 {
    let a = foo(x);
    a
}

#[refines(test_ghost_fields)]
pub fn test_ghost_fields2(x: i32) -> i32 {
    let (a, _) = foog(x);
    a
}
