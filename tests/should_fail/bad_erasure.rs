extern crate creusot_contracts;
use creusot_contracts::prelude::*;

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
