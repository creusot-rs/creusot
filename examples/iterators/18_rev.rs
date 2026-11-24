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
    fn produces_refl(self) {}

    #[logic(law)]
    #[allow(unused_variables)]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

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
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[allow(unused_variables)]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    fn next_back(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}
}

impl<I: ExactSizeIterator + DoubleEndedIterator> ExactSizeIterator for Rev<I> {
    #[logic(law)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        self.iter.size_hint_exact(r)
    }

    fn len(&self) -> usize {
        self.iter.len()
    }

    fn is_empty(&self) -> bool {
        proof_assert!(forall<s: Seq<I::Item>> s.len() == 0 ==> s == Seq::empty());
        self.iter.is_empty()
    }
}

#[ensures(result == Rev { iter })]
pub fn rev<I: Iterator>(iter: I) -> Rev<I> {
    Rev { iter }
}
