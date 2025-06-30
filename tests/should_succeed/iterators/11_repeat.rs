extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::Iterator;

#[derive(Resolve)]
pub struct Repeat<A> {
    pub element: A,
}

impl<A: Clone> Iterator for Repeat<A> {
    type Item = A;

    #[open]
    #[logic]
    fn completed(&mut self) -> bool {
        pearlite! { false }
    }

    #[open]
    #[logic]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self == o &&
            forall<i> 0 <= i && i < visited.len() ==> Self::Item::clone.postcondition((&self.element,), visited[i])
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
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
