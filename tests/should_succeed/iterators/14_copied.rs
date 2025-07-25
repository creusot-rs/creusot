#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::Iterator;

#[derive(Resolve)]
pub struct Copied<I> {
    pub iter: I,
}

impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    type Item = T;

    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() }
    }

    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>>
                   self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> visited[i] == *s[i]
        }
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
        self.iter.next().copied()
    }
}
