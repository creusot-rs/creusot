extern crate creusot_contracts;

use creusot_contracts::{invariant::Invariant, logic::Seq, *};

mod common;
use common::Iterator;

struct Zip<I, J> {
    iter1: I,
    iter2: J,
}

impl<I: Iterator, J: Iterator> Iterator for Zip<I, J> {
    type Item = (I::Item, J::Item);

    #[predicate]
    fn completed(&mut self) -> bool {
        self.iter1.completed() || self.iter2.completed()
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            // Using an `unzip` definition doesn't work well because of issues related to datatypes and `match`
            exists<p1 : Seq<_>, p2 : Seq<_>>
            p1.len() == p2.len() && p2.len() == visited.len() &&
            (forall<i :_> 0 <= i && i < visited.len() ==> visited[i] == (p1[i], p2[i])) &&
            self.iter1.produces(p1, tl.iter1) && self.iter2.produces(p2, tl.iter2)
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
      Some(v) => self.produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match (self.iter1.next(), self.iter2.next()) {
            (Some(i1), Some(i2)) => Some((i1, i2)),
            _ => None,
        }
    }
}

impl<I: Iterator, J: Iterator> Invariant for Zip<I, J> {
    #[predicate]
    fn invariant(self) -> bool {
        self.iter1.invariant() && self.iter2.invariant()
    }
}
