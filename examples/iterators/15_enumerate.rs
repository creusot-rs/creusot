extern crate creusot_std;
use creusot_std::{invariant::Invariant, prelude::*};

pub mod common;
pub use common::{ExactSizeIterator, Iterator};

pub struct Enumerate<I: Iterator> {
    pub iter: I,
    pub count: usize,
}

impl<I: Iterator> Iterator for Enumerate<I> {
    type Item = (usize, I::Item);

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() && resolve(&mut self.count) }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.count@ - self.count@
            && exists<s: Seq<I::Item>>
                   self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> visited[i].0@ == self.count@ + i && visited[i].1 == s[i]
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
    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next() {
            None => None,
            Some(x) => {
                let n = self.count;
                self.count += 1;
                Some((n, x))
            }
        }
    }

    #[ensures(I::size_hint.postcondition((&self.iter,), result))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I: ExactSizeIterator> ExactSizeIterator for Enumerate<I> {
    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        self.iter.size_hint_exact(r)
    }

    #[ensures(Self::size_hint.postcondition((self,), (result, Some(result))))]
    fn len(&self) -> usize {
        self.iter.len()
    }

    #[ensures(exists<l> Self::size_hint.postcondition((self,), (l, Some(l))) && result == (l == 0usize))]
    fn is_empty(&self) -> bool {
        proof_assert!(forall<s: Seq<I::Item>> s.len() == 0 ==> s == Seq::empty());
        self.iter.is_empty()
    }
}

impl<I: Iterator> Invariant for Enumerate<I> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<s: Seq<I::Item>, i: I>
                #[trigger(self.iter.produces(s, i))]
                self.iter.produces(s, i) ==>
                self.count@ + s.len() < std::usize::MAX@)
            && (forall<i: &mut I> i.completed() ==> i.produces(Seq::empty(), ^i))
        }
    }
}

// These two requirements are here only to prove the absence of overflow.
#[requires(forall<i: &mut I> i.completed() ==> i.produces(Seq::empty(), ^i))]
#[requires(forall<s: Seq<I::Item>, i: I> iter.produces(s, i) ==> s.len() < std::usize::MAX@)]
#[ensures(result.iter == iter && result.count@ == 0)]
pub fn enumerate<I: Iterator>(iter: I) -> Enumerate<I> {
    Enumerate { iter, count: 0 }
}
