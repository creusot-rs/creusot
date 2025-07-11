// WHY3PROVE
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::Iterator;

pub struct Empty<T>(std::marker::PhantomData<T>);

impl<T> Iterator for Empty<T> {
    type Item = T;

    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() }
    }

    #[open]
    #[logic]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { visited == Seq::empty() && self == o }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::empty(), self))]
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
    fn next(&mut self) -> Option<T> {
        None
    }
}
