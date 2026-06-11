extern crate creusot_std;
use creusot_std::{logic::Seq, prelude::*};

pub mod common;
use common::{DoubleEndedIterator, ExactSizeIterator, Iterator};

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
            && forall<i> 0 <= i && i < visited.len() ==> visited[i]@ == self.start@ + i
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
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
}

impl DoubleEndedIterator for Range {
    #[logic(open)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.start == o.start && self.end >= o.end
            && (visited.len() > 0 ==> o.end >= o.start)
            && visited.len() == self.end@ - o.end@
            && forall<i> 0 <= i && i < visited.len() ==> visited[i]@ == self.end@ - i - 1
        }
    }

    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.completed()
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}

    #[ensures(match result {
        None => self.completed_back(),
        Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
    })]
    fn next_back(&mut self) -> Option<isize> {
        if self.start >= self.end {
            None
        } else {
            self.end -= 1;
            Some(self.end)
        }
    }
}

impl Range {
    #[ensures(result == self)]
    pub fn into_iter(self) -> Self {
        self
    }
}

pub struct RangeInclusive {
    pub start: i32,
    pub end: i32,
    exhausted: bool,
}

impl RangeInclusive {
    #[logic]
    #[ensures(start == result.start)]
    #[ensures(end == result.end)]
    #[ensures(start <= end ==> !result.is_empty_log())]
    pub fn new_log(start: i32, end: i32) -> Self {
        RangeInclusive { start, end, exhausted: false }
    }

    #[ensures(result == Self::new_log(start, end))]
    pub fn new(start: i32, end: i32) -> Self {
        RangeInclusive { start, end, exhausted: false }
    }

    #[logic]
    pub fn is_empty_log(self) -> bool {
        self.start > self.end || self.exhausted
    }

    #[ensures(result == self.is_empty_log())]
    pub fn is_empty(&self) -> bool {
        self.exhausted || !(self.start <= self.end)
    }

    #[logic(open)]
    pub fn len_log(self) -> Int {
        pearlite! {
            if self.is_empty_log() { 0 } else { self.end@ - self.start@ + 1 }
        }
    }
}

impl Iterator for RangeInclusive {
    type Item = i32;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.is_empty_log() && (^self).is_empty_log()
        }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == self.len_log() - o.len_log() &&
            (self.is_empty_log() ==> o.is_empty_log()) &&
            (o.is_empty_log() || self.end == o.end) &&
            forall<i> 0 <= i && i < visited.len() ==> visited[i]@ == self.start@ + i
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
    fn next(&mut self) -> Option<i32> {
        if self.is_empty() {
            return None;
        }
        let is_iterating = self.start < self.end;
        Some(if is_iterating {
            let r = self.start;
            self.start += 1;
            r
        } else {
            self.exhausted = true;
            self.start
        })
    }

    #[bitwise_proof]
    #[ensures(self.len_log() <= usize::MAX@ ==> result.0@ == self.len_log() && result.1 == Some(result.0))]
    #[ensures(self.len_log() > usize::MAX@ ==> result == (usize::MAX, None))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.is_empty() {
            return (0, Some(0));
        }
        let steps = (self.end as isize).wrapping_sub(self.start as isize) as usize + 1;
        proof_assert!(
            (self.end - self.start) as u32 as isize == self.end as isize - self.start as isize
        );
        (steps, Some(steps))
    }
}

impl ExactSizeIterator for RangeInclusive {
    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
}

impl DoubleEndedIterator for RangeInclusive {
    #[logic(open)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == self.len_log() - o.len_log() &&
            (self.is_empty_log() ==> o.is_empty_log()) &&
            (o.is_empty_log() || self.start == o.start) &&
            forall<i> 0 <= i && i < visited.len() ==> visited[i]@ == self.end@ - i
        }
    }

    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.completed()
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}

    #[ensures(match result {
        None => self.completed_back(),
        Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
    })]
    fn next_back(&mut self) -> Option<i32> {
        if self.is_empty() {
            return None;
        }
        let is_iterating = self.start < self.end;
        Some(if is_iterating {
            let r = self.end;
            self.end -= 1;
            r
        } else {
            self.exhausted = true;
            self.end
        })
    }
}

impl RangeInclusive {
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
