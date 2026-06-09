extern crate creusot_std;
use creusot_std::prelude::*;

pub mod common;
pub use common::{ExactSizeIterator, Iterator};

pub struct Copied<I> {
    pub iter: I,
}

impl<'a, I: Iterator<Item = &'a T>, T: Copy + 'a> Iterator for Copied<I> {
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
                && forall<i> 0 <= i && i < s.len() ==> visited[i] == *s[i]
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
        self.iter.next().copied()
    }

    #[ensures(I::size_hint.postcondition((&self.iter,), result))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, I: ExactSizeIterator<Item = &'a T>, T: Copy + 'a> ExactSizeIterator for Copied<I> {
    #[logic(law)]
    #[ensures(forall<r> Self::size_hint.postcondition((&self,), r) ==> r.1 == Some(r.0))]
    fn size_is_exact(self) {
        self.iter.size_is_exact()
    }

    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces(s, *i) && i.completed() ==> result@ == s.len())]
    #[ensures(forall<s: Seq<Self::Item>, i: Self>
        self.produces(s, i) ==> s.len() <= result@)]
    fn len(&self) -> usize {
        self.iter.len()
    }

    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces(s, *i) && i.completed() ==> result == (s == Seq::empty()))]
    #[ensures(forall<s: Seq<Self::Item>, i: Self>
        self.produces(s, i) && result ==> s == Seq::empty())]
    fn is_empty(&self) -> bool {
        proof_assert!(forall<s: Seq<I::Item>> s.len() == 0 ==> s == Seq::empty());
        self.iter.is_empty()
    }
}
