#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::*;

struct Range {
    start: isize,
    end: isize,
}

impl Iterator for Range {
    type Item = isize;

    #[predicate]
    fn completed(self) -> bool {
        pearlite! { self.start >= self.end }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.end == o.end && self.start <= o.start
            &&  visited.len() == @(o.start) - @(self.start)
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                @(visited[i]) == @self.start + i
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

    // #[requires(!(*self).completed())]
    #[ensures(match result {
      None => (^self).completed() && self.resolve(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self) && !(*self).completed()
    })]
    fn next(&mut self) -> Option<isize> {
        if self.start >= self.end {
            None
        } else {
            let r = self.start;
            self.start += 1;
            Some(r)
        }
    }
}

#[requires(@n >= 0)]
#[ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    {
        // the for loop
        let mut it = Range { start: 0, end: n };
        let it_old = ghost! { &it };
        let mut produced = ghost! { Seq::EMPTY };
        #[invariant(free, (it_old).produces(produced.inner(), it))]
        // user invariant
        #[invariant(user, @i == produced.len() && i <= n)]
        loop {
            match it.next() {
                Some(j) => {
                    produced = ghost! { produced.push(j) };
                    i += 1;
                }
                None => break,
            }
        }
    }
    i
}
