extern crate creusot_std;
use creusot_std::prelude::*;

mod common;
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

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self == o &&
            forall<i> 0 <= i && i < visited.len() ==> Self::Item::clone.postcondition((&self.element,), visited[i])
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<A> {
        Some(self.element.clone())
    }
}
