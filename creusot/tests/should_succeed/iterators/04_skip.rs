#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::Iterator;

pub struct Skip<I> {
    iter: I,
    n: usize,
}

impl<I> Iterator for Skip<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            @(^self).n == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I>
                s.len() <= @self.n &&
                self.iter.produces(s, *i) &&
                i.completed() &&
                ^i == (^self).iter
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            @o.n == 0 &&
            exists<s: Seq<Self::Item>>
                s.len() == @self.n &&
                self.iter.produces(s.concat(visited), o.iter)
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[predicate]
    fn invariant(self) -> bool {
        self.iter.invariant()
    }

    #[maintains((mut self).invariant())]
    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<I::Item> {
        let old_self = ghost! { self };
        let mut n = std::mem::take(&mut self.n);
        #[invariant(proph_const, ^self == ^old_self.inner())]
        #[invariant(produces, exists<s : Seq<Self::Item>> s.len() + @n == @old_self.n
                              && old_self.iter.produces(s, self.iter))]
        #[invariant(n_0, @(*self).n == 0)]
        #[invariant(inv, self.invariant())]
        loop {
            let r = self.iter.next();
            if n == 0 || r.is_none() {
                return r;
            }
            n -= 1
        }
    }
}
