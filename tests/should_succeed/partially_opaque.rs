extern crate creusot_contracts;
use creusot_contracts::prelude::*;

mod m {
    use creusot_contracts::prelude::*;

    pub struct S<A, B> {
        pub a: A,
        #[allow(unused)]
        b: B,
    }

    impl<B> Invariant for S<i32, B> {
        #[logic(prophetic, open)]
        fn invariant(self) -> bool {
            pearlite! { self.a@ % 2 == 0 }
        }
    }
}
use m::*;

#[ensures(resolve(x.a) ==> resolve(x))]
pub fn f<A, B>(x: S<A, B>) -> A {
    x.a
}

pub fn g<B>(x: &mut S<i32, B>) {
    x.a = 34;
}
