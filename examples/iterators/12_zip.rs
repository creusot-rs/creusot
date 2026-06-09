extern crate creusot_std;

use creusot_std::{logic::Seq, prelude::*};

pub mod common;
use common::{ExactSizeIterator, Iterator};

#[allow(dead_code)]
struct Zip<A: Iterator, B: Iterator> {
    pub a: A,
    pub b: B,
}

impl<A: Iterator, B: Iterator> Iterator for Zip<A, B> {
    type Item = (A::Item, B::Item);

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
             (self.a.completed() && (*self).b == (^self).b)
          || (exists<x: A::Item> self.a.produces(Seq::singleton(x), (^self).a) &&
                                 resolve(x) && self.b.completed())
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            // Using an `unzip` definition doesn't work well because of issues related to datatypes and `match`
            exists<p1: Seq<_>, p2: Seq<_>>
                   p1.len() == p2.len() && p2.len() == visited.len()
                && (forall<i> 0 <= i && i < visited.len() ==> visited[i] == (p1[i], p2[i]))
                && self.a.produces(p1, tl.a) && self.b.produces(p2, tl.b)
        }
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
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

    #[ensures(exists<ra, rb>
        A::size_hint.postcondition((&self.a,), ra) &&
        B::size_hint.postcondition((&self.b,), rb) &&
        (ra.0@ <= rb.0@ ==> result.0 == ra.0) &&
        (ra.0@ >= rb.0@ ==> result.0 == rb.0) &&
        match (ra.1, rb.1) {
            (Some(ua), Some(ub)) =>
                (ua@ <= ub@ ==> result.1 == Some(ua)) &&
                (ua@ >= ub@ ==> result.1 == Some(ub)),
            (Some(ua), None) => result.1 == Some(ua),
            (None, Some(ub)) => result.1 == Some(ub),
            (None, None) => result.1 == None
        }
    )]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_lower, a_upper) = self.a.size_hint();
        let (b_lower, b_upper) = self.b.size_hint();

        let lower = std::cmp::min(a_lower, b_lower);

        let upper = match (a_upper, b_upper) {
            (Some(x), Some(y)) => Some(std::cmp::min(x, y)),
            (Some(x), None) => Some(x),
            (None, Some(y)) => Some(y),
            (None, None) => None,
        };

        (lower, upper)
    }
}

impl<A: ExactSizeIterator, B: ExactSizeIterator> ExactSizeIterator for Zip<A, B> {
    #[logic(law)]
    #[ensures(forall<r> Self::size_hint.postcondition((&self,), r) ==> r.1 == Some(r.0))]
    fn size_is_exact(self) {
        self.a.size_is_exact();
        self.b.size_is_exact();
    }
}
