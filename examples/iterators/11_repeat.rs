extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
pub use common::Iterator;

pub struct Repeat<A> {
    pub element: A,
}

impl<A: Clone> Iterator for Repeat<A> {
    type Item = A;

    #[logic(open)]
    fn completed(&mut self) -> bool {
        pearlite! { false }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self == o &&
            forall<i> 0 <= i && i < visited.len() ==> Self::Item::clone.postcondition((&self.element,), visited[i])
        }
    }

    #[logic(open, law)]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[allow(unused_variables)]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    fn next(&mut self) -> Option<A> {
        Some(self.element.clone())
    }

    #[ensures(result == (usize::MAX, None))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (usize::MAX, None)
    }
}
