extern crate creusot_contracts;
use creusot_contracts::*;

pub trait A {
    fn f(&self) -> Self;
}

impl A for i32 {
    fn f(&self) -> Self {
        0
    }
}

pub trait B: Sized {
    #[ensures(result == result)]
    fn g(&self) -> Self;
}

impl B for u32 {
    fn g(&self) -> Self {
        1
    }
}

pub trait C {
    fn h<T>(x: &T) -> &T;
}

impl C for u32 {
    fn h<G>(y: &G) -> &G {
        y
    }
}
