#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, *};

mod common;
use common::Iterator;

pub struct Skip<I> {
    iter: I,
    n: usize,
}

impl<I> Invariant for Skip<I>
where
    I: Iterator,
{
    #[predicate]
    #[creusot::type_invariant]
    fn invariant(self) -> bool {
        self.iter.invariant()
    }
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
                (forall<i: Int> 0 <= i && i < s.len() ==> s[i].resolve()) &&
                i.completed() &&
                ^i == (^self).iter
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            @o.n == 0 && visited.len() > 0 &&
            exists<s: Seq<Self::Item>>
                s.len() == @self.n &&
                self.iter.produces(s.concat(visited), o.iter) &&
                forall<i: Int> 0 <= i && i < s.len() ==> s[i].resolve()
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
    fn next(&mut self) -> Option<I::Item> {
        let old_self = ghost! { self };
        let mut n = std::mem::take(&mut self.n);
        let mut skipped = ghost! { Seq::EMPTY };
        #[invariant(skipped_len, skipped.len() + @n == @old_self.n)]
        #[invariant(produces, old_self.iter.produces(skipped.inner(), self.iter))]
        #[invariant(skipped_resolve, forall<i: Int> 0 <= i && i < skipped.len() ==> skipped[i].resolve())]
        #[invariant(n_0, @(*self).n == 0)]
        #[invariant(inv, self.invariant())]
        loop {
            let r = self.iter.next();
            if n == 0 {
                return r;
            }
            if let Some(x) = r {
                skipped = ghost! { skipped.concat(Seq::singleton(x)) };
                n -= 1
            } else {
                return r;
            }
        }
    }
}
