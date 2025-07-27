extern crate creusot_contracts;
use creusot_contracts::*;

pub trait One: Sized {
    #[logic]
    #[ensures(forall<x: Self, y: Self> x == y)]
    fn one();
}

pub trait Tr: Sized {
    #[law]
    #[ensures(forall<x: Self, y: Self> x == y)]
    fn a(self)
    where
        Self: One;

    #[logic]
    fn f(self) -> Self;
}

mod m {
    use One;
    use Tr;
    use creusot_contracts::*;

    impl<T> Tr for T {
        #[law]
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
