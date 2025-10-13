extern crate creusot_contracts;
use creusot_contracts::{ghost::PtrOwn, *};

fn foo(x: i32) -> i32 {
    x
}

#[erasure(foo)]
fn foo2(x: i32, _: Ghost<Int>) -> i32 {
    x
}

#[trusted]
#[erasure(foo)]
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

#[erasure(<i32 as Quux>::quux)]
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

#[erasure(test_foo)]
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

#[erasure(<i32 as Tr>::takes_ref)]
fn takes_ref(x: &i32) -> i32 {
    *x
}

pub fn takes_ref_test(x: i32) -> i32 {
    // Autoref makes this `(&x).takes_ref()`
    x.takes_ref()
}

#[erasure(takes_ref_test)]
pub fn takes_ref_test2(x: i32) -> i32 {
    // THIR introduces a reborrow, making this `takes_ref(&*&x)`
    takes_ref(&x)
}

#[erasure(foo)]
fn foog(x: i32) -> (i32, Ghost<i32>) {
    (x, ghost!(x))
}

pub fn test_ghost_fields(x: i32) -> i32 {
    let a = foo(x);
    a
}

#[erasure(test_ghost_fields)]
pub fn test_ghost_fields2(x: i32) -> i32 {
    let (a, _) = foog(x);
    a
}

#[trusted]
pub unsafe fn test_ptr<'a, T>(x: *mut T) -> &'a T {
    unsafe { &*x }
}

#[erasure(test_ptr)]
#[requires(false)] // don't care about proofs
pub unsafe fn test_ptr2<T>(x: *mut T, own: Ghost<&PtrOwn<T>>) -> &T {
    unsafe { PtrOwn::as_ref(x, own) }
}

#[trusted]
pub unsafe fn test_ptr_mut<'a, T>(x: *mut T) -> &'a mut T {
    unsafe { &mut *x }
}

#[erasure(test_ptr_mut)]
#[requires(false)]
pub unsafe fn test_ptr_mut2<T>(x: *mut T, own: Ghost<&mut PtrOwn<T>>) -> &mut T {
    unsafe { PtrOwn::as_mut(x, own) }
}

pub fn no_specs() {
    let _ = foo(0);
    while false {}
}

#[erasure(no_specs)]
#[requires(false)]
#[ensures(false)]
pub fn specs(x: Snapshot<Int>) {
    proof_assert!(false);
    let _ = foo(0);
    let _ = snapshot!(*x);
    #[invariant(false)]
    while false {}
}

pub fn nested() {
    fn hidden() {}
    hidden()
}

#[erasure(nested)]
pub fn nested2() {
    fn hidden() {}
    hidden()
}

#[erasure(private crate::nested)]
pub fn nested3() {
    fn hidden() {}
    hidden()
}

pub fn ghost_split() {}

#[erasure(ghost_split)]
pub fn ghost_split2() {
    let (_, _) = ghost! { ((), ()) }.split();
}

pub fn slice_as_ptr<T>(s: &[T]) -> *const T {
    s.as_ptr()
}

#[erasure(slice_as_ptr)]
pub fn slice_as_ptr_own<T>(s: &[T]) -> (*const T, Ghost<&PtrOwn<[T]>>) {
    s.as_ptr_own()
}

pub fn slice_as_mut_ptr<T>(s: &mut [T]) -> *mut T {
    s.as_mut_ptr()
}

#[erasure(slice_as_mut_ptr)]
pub fn slice_as_mut_ptr_own<T>(s: &mut [T]) -> (*mut T, Ghost<&mut PtrOwn<[T]>>) {
    s.as_mut_ptr_own()
}
