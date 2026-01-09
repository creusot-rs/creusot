extern crate creusot_std;
use creusot_std::prelude::*;

pub trait One: Sized {
    #[logic]
    #[ensures(forall<x: Self, y: Self> x == y)]
    fn one();
}

pub trait Tr: Sized {
    #[logic(law)]
    #[ensures(forall<x: Self, y: Self> x == y)]
    fn a(self)
    where
        Self: One;

    #[logic]
    fn f(self) -> Self;
}

mod m {
    use crate::{One, Tr};
    use creusot_std::prelude::*;

    impl<T> Tr for T {
        #[logic(law)]
        #[ensures(forall<x: Self, y: Self> x == y)]
        fn a(self)
        where
            Self: One,
        {
            Self::one()
        }

        #[logic]
        fn f(self) -> Self {
            self
        }
    }
}

pub fn x() {
    proof_assert! { true.f() == true };
    proof_assert! { false }
}
