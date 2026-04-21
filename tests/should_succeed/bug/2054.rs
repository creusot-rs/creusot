extern crate creusot_std;
use creusot_std::prelude::*;

pub trait F {
    const C: Self;
}

pub struct S<T>(T);

impl<T: F> F for S<T> {
    const C: Self = const { S(T::C) };
}

#[ensures(result == S::C)]
pub fn f<T: F>() -> S<T> {
    S::C
}
