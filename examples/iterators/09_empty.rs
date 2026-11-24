extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
pub use common::{ExactSizeIterator, Iterator};

pub struct Empty<T>(std::marker::PhantomData<T>);

impl<T> Iterator for Empty<T> {
    type Item = T;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self) }
    }

    #[logic(open, inline)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { visited == Seq::empty() && self == o }
    }

    #[logic(open, law)]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[allow(unused_variables)]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    fn next(&mut self) -> Option<T> {
        None
    }

    #[ensures(result == (0usize, Some(0usize)))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(0))
    }
}

impl<T> ExactSizeIterator for Empty<T> {
    #[logic(law)]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
}
