extern crate creusot_std;
use creusot_std::{logic::Seq, prelude::*};

pub mod common;
use common::{DoubleEndedIterator, ExactSizeIterator, Iterator};

pub struct Rev<I> {
    pub iter: I,
}

impl<I: DoubleEndedIterator> Iterator for Rev<I> {
    type Item = I::Item;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        self.iter.completed_back()
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        self.iter.produces_back(visited, o.iter)
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next_back()
    }

    #[ensures(I::size_hint.postcondition((&self.iter,), result))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<I: DoubleEndedIterator> DoubleEndedIterator for Rev<I> {
    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.iter.completed()
    }

    #[logic(open, prophetic)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        self.iter.produces(visited, o.iter)
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
        None => self.completed_back(),
        Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
    })]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

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
}

impl<I: ExactSizeIterator + DoubleEndedIterator> ExactSizeIterator for Rev<I> {
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

#[ensures(result == Rev { iter })]
pub fn rev<I: Iterator>(iter: I) -> Rev<I> {
    Rev { iter }
}
