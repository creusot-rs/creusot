// Recursion through trait impls (issue #1232)
extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr1 {
    #[logic]
    fn f();
}

pub trait Tr2 {
    #[logic]
    fn g();
}

impl<T> Tr1 for T
where
    T: Tr2,
{
    #[logic]
    fn f() {
        T::g()
    }
}

impl Tr2 for u32 {
    #[logic]
    fn g() {
        f0::<u32>()
    }
}

#[logic]
pub fn f0<T: Tr1>() {
    T::f()
}
