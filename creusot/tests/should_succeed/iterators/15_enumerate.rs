#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, *};

mod common;
use common::Iterator;

pub struct Enumerate<I> {
    iter: I,
    count: usize,
}

impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    type Item = (usize, I::Item);

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.count@ - @self.count
            && exists<s: Seq<I::Item>> self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i].0@ == self.count@ + i && visited[i].1 == s[i]
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
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
    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.iter.invariant()
            && (forall<s: Seq<I::Item>, i: I> self.iter.produces(s, i) ==> self.count@ + s.len() < std::usize::MAX@)
            && (forall<i: &mut I> i.completed() ==> i.produces(Seq::EMPTY, ^i))
        }
    }
}

#[requires(forall<i: &mut I> i.completed() ==> i.produces(Seq::EMPTY, ^i))]
#[requires(forall<s: Seq<I::Item>, i: I> iter.produces(s, i) ==> s.len() < std::usize::MAX@)]
pub fn enumerate<I: Iterator>(iter: I) -> Enumerate<I> {
    Enumerate { iter, count: 0 }
}
