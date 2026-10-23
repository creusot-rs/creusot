extern crate creusot_std;
use creusot_std::prelude::*;

pub fn baz<const N: i32>() -> i32 {
    N
}

#[erasure(baz::<N>)]
pub fn baz2<const N: i32>() -> i32 {
    N
}

pub fn bar() -> i32 {
    baz::<42>()
}

#[erasure(bar)]
pub fn bar2() -> i32 {
    baz::<0>()
}

#[erasure(bar)]
pub fn bar3() -> i32 {
    baz2::<0>()
}

pub fn add(x: usize, y: usize) -> usize {
    x + y
}

#[erasure(add)]
pub fn add2(x: usize, y: usize) -> usize {
    x + x
}

pub trait Quux {
    fn quux();
}

#[erasure(T::quux)]
pub fn quux2<T: Quux>() {}

#[allow(unused)]
pub struct P {
    a: usize,
    b: usize,
}

pub fn q() -> usize {
    0
}

pub fn p() -> P {
    P { a: q(), b: q() }
}

// Wrong if `q` returns different values.
#[erasure(p)]
pub fn p2() -> P {
    P { b: q(), a: q() }
}
