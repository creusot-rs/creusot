// TACTIC +inline_goal
extern crate creusot_std;
use creusot_std::prelude::*;

mod common;
pub use common::Iterator;

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
}
