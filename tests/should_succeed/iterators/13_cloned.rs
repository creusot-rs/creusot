#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::Iterator;

#[derive(Resolve)]
pub struct Cloned<I: Iterator> {
    pub iter: I,
}

impl<'a, I, T: 'a> Iterator for Cloned<I>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    type Item = T;

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>>
                   self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> T::clone.postcondition((s[i],), visited[i])
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
    fn next(&mut self) -> Option<T> {
        self.iter.next().cloned()
    }
}
