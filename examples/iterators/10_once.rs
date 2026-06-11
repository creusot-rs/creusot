// TACTIC +inline_goal
extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
use common::{ExactSizeIterator, Iterator};

pub struct Once<T>(pub Option<T>);

impl<T> Iterator for Once<T> {
    type Item = T;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { *self == Once(None) && resolve(self) }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            exists<e: Self::Item> self == Once(Some(e)) && visited == Seq::singleton(e) && o == Once(None)
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
    fn next(&mut self) -> Option<T> {
        self.0.take()
    }

    #[ensures(result.0 == match self.0 { Some(_) => 1usize, None => 0usize })]
    #[ensures(result.1 == Some(result.0))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = match self.0 {
            Some(_) => 1,
            None => 0,
        };
        (l, Some(l))
    }
}

impl<T> ExactSizeIterator for Once<T> {
    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}

    #[ensures(Self::size_hint.postcondition((self,), (result, Some(result))))]
    fn len(&self) -> usize {
        match self.0 {
            Some(_) => 1,
            None => 0,
        }
    }
}
