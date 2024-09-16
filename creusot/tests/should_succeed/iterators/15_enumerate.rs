#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{inv, Invariant},
    *,
};

mod common;
use common::Iterator;

pub struct Enumerate<I: Iterator> {
    iter: I,
    count: usize,
}

impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    type Item = (usize, I::Item);

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.count@ - self.count@
            && exists<s: Seq<I::Item>> inv(s)
                && self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i].0@ == self.count@ + i && visited[i].1 == s[i]
        }
    }

    #[law]
    #[open]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            None => None,
            Some(x) => {
                let n = self.count;
                self.count += 1;
                Some((n, x))
            }
        }
    }
}

impl<I> Invariant for Enumerate<I>
where
    I: Iterator,
{
    #[open]
    #[predicate(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<s: Seq<I::Item>, i: I> self.iter.produces(s, i) ==> self.count@ + s.len() < std::usize::MAX@)
            && (forall<i: &mut I> i.completed() ==> i.produces(Seq::EMPTY, ^i))
        }
    }
}

#[requires(forall<i: &mut I> i.completed() ==> i.produces(Seq::EMPTY, ^i))]
#[requires(forall<s: Seq<I::Item>, i: I> iter.produces(s, i) ==> s.len() < std::usize::MAX@)]
pub fn enumerate<I: Iterator>(iter: I) -> Enumerate<I> {
    Enumerate { iter, count: 0 }
}
