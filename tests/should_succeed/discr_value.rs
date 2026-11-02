#![feature(core_intrinsics)]

use creusot_std::prelude::*;

pub enum Foo {
    A,
    B = 3,
    C,
    D = 10,
}

#[ensures(result@ == f.discr())]
pub fn program(f: Foo) -> u32 {
    f as u32
}

#[logic]
#[ensures(result@ == f.discr())]
pub fn logic(f: Foo) -> u32 {
    f as u32
}

impl Foo {
    #[logic(open, inline)]
    fn discr(self) -> Int {
        match self {
            Self::A => 0,
            Self::B => 3,
            Self::C => 4,
            Self::D => 10,
        }
    }
}

pub fn use_intrinsic<T>(v: &T) -> impl Sized {
    std::intrinsics::discriminant_value(v)
}
