// WHY3PROVE
extern crate creusot_std;
use creusot_std::prelude::*;

// Check against two bugs:
// 1. the default impl should not be picked.
// 2. the const setters should be placed under the abstraction barrier.
pub trait G {
    const N: usize = 0;
}

struct S<T>(T);

impl<T: G> G for S<T> {
    // check the overflow at every use site
    const N: usize = const { T::N + 1 };
}

#[ensures(result != 0usize)]
pub fn g<T: G>() -> usize {
    S::<T>::N
}

#[logic]
#[ensures(result != 0usize)]
pub fn gl<T: G>() -> usize {
    S::<T>::N
}
