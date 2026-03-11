extern crate creusot_std;

use creusot_std::prelude::*;

pub fn assertion<T>(x: T) {
    proof_assert! { x == x };
}

#[ensures(b)]
pub fn assume(b: bool) {
    #[trusted]
    proof_assert! { b };
}

#[ensures(|(fst, snd)| fst == snd)]
pub fn apair(result: i64) -> (i64, i64) {
    (result, result)
}
