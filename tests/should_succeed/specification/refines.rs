extern crate creusot_contracts;
use creusot_contracts::{ghost::PtrOwn, *};

fn foo(x: i32) -> i32 {
    x
}

#[refines(foo)]
fn foo2(x: i32, _: Ghost<Int>) -> i32 {
    x
}

#[trusted]
#[refines(foo)]
pub fn foo3(x: i32) -> i32 {
    foo(x)
}

fn baz<const N: i32>() -> i32 {
    N
}

trait Quux {
    fn quux(&self);
}

impl Quux for i32 {
    fn quux(&self) {
        let _ = foo(*self);
    }
}

#[refines(<i32 as Quux>::quux)]
fn quux2(x: &i32, y: Ghost<Int>) {
    let _ = foo2(*x, y);
}

pub fn test_foo(x: i32) -> i32 {
    let a = foo(x);
    let b = foo(a);
    let c = baz::<42>();
    c.quux();
    if -10 < a && a < 10 && -10 < b && b < 10 { a + b } else { c }
}

#[refines(test_foo)]
pub fn test_foo2(x: i32, y: Ghost<Int>) -> i32 {
    let a = foo(x);
    let b = foo2(a, y);
    let c = baz::<42>();
    quux2(&c, y);
    if -10 < a && a < 10 && -10 < b && b < 10 { a + b } else { c }
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

#[trusted]
pub unsafe fn test_ptr<'a, T>(x: *mut T) -> &'a T {
    unsafe { &*x }
}

#[refines(test_ptr)]
pub unsafe fn test_ptr2<T>(x: *mut T, own: Ghost<&PtrOwn<T>>) -> &T {
    unsafe { PtrOwn::as_ref(x, own) }
}

#[trusted]
pub unsafe fn test_ptr_mut<'a, T>(x: *mut T) -> &'a mut T {
    unsafe { &mut *x }
}

#[refines(test_ptr_mut)]
pub unsafe fn test_ptr_mut2<T>(x: *mut T, own: Ghost<&mut PtrOwn<T>>) -> &mut T {
    unsafe { PtrOwn::as_mut(x, own) }
}
