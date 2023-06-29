extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

pub trait T {
    type Output;
}

impl T for () {
    type Output = (u32, u32);
}

pub struct S{f: <() as T>::Output}

#[ensures(result == x.0)]
pub fn test_arg<X: T<Output=(u32, u32)>>(x: X::Output) -> u32 {
    x.0
}

#[ensures(result == x.f.0)]
pub fn test_struct(x: S) -> u32 {
    x.f.0
}

#[open]
#[logic]
pub fn test_ret<X: T>() -> Option<X::Output> {
    None
}

#[ensures(match test_ret::<()>() {None => true, Some((x, y)) => x > y})]
pub fn test_call() {}
