#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, *};

mod common;
use common::Iterator;

pub struct Copied<I> {
    iter: I,
}

impl<'a, I, T: 'a> Iterator for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    type Item = T;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>> self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i] == *s[i]
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

    #[maintains((mut self).invariant())]
    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<T> {
        self.iter.next().copied()
    }
}

impl<'a, I, T: 'a> Invariant for Copied<I>
where
    I: Iterator<Item = &'a T>,
    T: Copy,
{
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        pearlite! {
            self.iter.invariant()
        }
    }
}
