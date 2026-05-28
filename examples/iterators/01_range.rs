extern crate creusot_std;
use creusot_std::{logic::Seq, prelude::*};

pub mod common;
use common::{ExactSizeIterator, Iterator};

struct Range {
    pub start: isize,
    pub end: isize,
}

impl Iterator for Range {
    type Item = isize;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            resolve(self) && self.start >= self.end
        }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.end == o.end && self.start <= o.start
            && (visited.len() > 0 ==> o.start <= o.end)
            && visited.len() == o.start@ - self.start@
            && forall<i> 0 <= i && i < visited.len() ==>
                visited[i]@ == self.start@ + i
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
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
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

    #[bitwise_proof]
    #[ensures(self.start.deep_model() >= self.end.deep_model() ==>
        result == (0usize, Some(0usize)))]
    #[ensures({
        let s = self.end.deep_model() - self.start.deep_model();
        s >= 0 && s <= usize::MAX@ ==>
        result.0@ == s && result.1 == Some(result.0)
    })]
    #[ensures(self.end.deep_model() - self.start.deep_model() > usize::MAX@ ==>
        result == (usize::MAX, None))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.start < self.end {
            let steps = self.end.wrapping_sub(self.start) as usize;
            (steps, Some(steps))
        } else {
            (0, Some(0))
        }
    }
}

impl ExactSizeIterator for Range {
    #[logic(law)]
    #[ensures(forall<r> Self::size_hint.postcondition((&self,), r) ==> r.1 == Some(r.0))]
    fn size_is_exact(self) {}
}

impl Range {
    #[ensures(result == self)]
    pub fn into_iter(self) -> Self {
        self
    }
}

#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn sum_range(n: isize) -> isize {
    let mut i = 0;
    let mut it = Range { start: 0, end: n }.into_iter();
    let iter_old = snapshot! { it };
    let mut produced = snapshot! { Seq::empty() };
    #[invariant(iter_old.produces(produced.inner(), it))]
    #[invariant(i@ == produced.len() && i <= n)]
    loop {
        match it.next() {
            Some(x) => {
                produced = snapshot! { produced.concat(Seq::singleton(x)) };
                i += 1
            }
            None => break,
        }
    }
    i
}
