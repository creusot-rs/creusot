extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn f(self) -> Int;
}

impl Tr for i32 {
    #[logic]
    fn f(self) -> Int {
        g()
    }
}

#[logic]
pub fn g() -> Int
where
    i32: Tr,
{
    1i32.f()
}
