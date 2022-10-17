#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::Iterator;

pub struct Take<I> {
    iter: I,
    n: usize,
}

impl<I> Iterator for Take<I>
where
    I: Iterator,
{
    type Item = I::Item;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            @(*self).n == 0 && self.resolve() ||
            @(*self).n > 0 && @(*self).n == @(^self).n + 1 &&
            // FIXME : remove this quantification by unnesting
                exists<i: &mut I> *i == (*self).iter && ^i == (^self).iter && i.completed()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            @self.n == @o.n + visited.len() && self.iter.produces(visited, o.iter)
        }
    }

    #[predicate]
    fn invariant(self) -> bool {
        pearlite! {
            self.iter.invariant()
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

    #[maintains((mut self).invariant())]
    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<I::Item> {
        if self.n != 0 {
            self.n -= 1;
            self.iter.next()
        } else {
            None
        }
    }
}
