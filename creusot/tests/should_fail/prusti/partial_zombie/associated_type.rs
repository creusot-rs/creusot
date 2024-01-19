extern crate creusot_contracts;
use creusot_contracts::prusti_prelude::*;

trait T {
    type A;
}

impl T for u32 {
    type A = Box<u32>;
}

impl T for Box<u32> {
    type A = u32;
}

impl<A: T, B: T> T for (A, B) {
    type A = (A::A, B::A);
}
type A<X> = <X as T>::A;
#[ensures(x == x)]
fn test<X: T>(x: (A<X>, A<u32>, A<Box<u32>>, A<(X, u32)>)) {}
