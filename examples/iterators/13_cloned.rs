extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
pub use common::{ExactSizeIterator, Iterator};

pub struct Cloned<I: Iterator> {
    pub iter: I,
}

impl<'a, I: Iterator<Item = &'a T>, T: Clone + 'a> Iterator for Cloned<I> {
    type Item = T;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter.completed() }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>>
                   self.iter.produces(s, o.iter)
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> T::clone.postcondition((s[i],), visited[i])
        }
    }

    #[logic(open, law)]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[allow(unused_variables)]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    fn next(&mut self) -> Option<T> {
        self.iter.next().cloned()
    }

    #[ensures(I::size_hint.postcondition((&self.iter,), result))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, I: ExactSizeIterator<Item = &'a T>, T: Clone + 'a> ExactSizeIterator for Cloned<I> {
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
