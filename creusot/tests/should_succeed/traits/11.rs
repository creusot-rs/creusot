extern crate creusot_contracts;

use creusot_contracts::*;

#[logic]
fn id<T>(x: T) -> T {
    x
}

trait A {
    type T;

    #[ensures(id(x) == x)]
    fn f(x: Self::T);
}

fn test<T: A>(_: T) {}
