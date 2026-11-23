extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

impl FromIterator<()> for S {
    #[requires(true)]
    fn from_iter<I: IntoIterator<Item = ()>>(_: I) -> Self {
        S
    }
}

pub fn f() {
    let _ = S::from_iter([()].into_iter());
}
