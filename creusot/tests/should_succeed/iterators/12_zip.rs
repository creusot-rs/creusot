extern crate creusot_contracts;

use creusot_contracts::{logic::Seq, *};

mod common;
use common::Iterator;

struct Zip<A: Iterator, B: Iterator> {
    a: A,
    b: B,
}

impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    type Item = (A::Item, B::Item);

    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
             (self.a.completed() && (*self).b == (^self).b)
          || (exists<x: A::Item> self.a.produces(Seq::singleton(x), (^self).a) &&
                                 x.resolve() && self.b.completed())
        }
    }

    #[open]
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            // Using an `unzip` definition doesn't work well because of issues related to datatypes and `match`
            exists<p1 : Seq<_>, p2 : Seq<_>>
            p1.len() == p2.len() && p2.len() == visited.len() &&
            (forall<i :_> 0 <= i && i < visited.len() ==> visited[i] == (p1[i], p2[i])) &&
            self.a.produces(p1, tl.a) && self.b.produces(p2, tl.b)
        }
    }

    #[law]
    #[open]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => self.produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        let x = match self.a.next() {
            None => return None,
            Some(x) => x,
        };
        let y = match self.b.next() {
            None => return None,
            Some(y) => y,
        };
        Some((x, y))
    }
}
