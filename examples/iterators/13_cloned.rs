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
