extern crate creusot_std;
use creusot_std::{invariant::Invariant, logic::Seq, prelude::*};

pub mod common;
use common::{DoubleEndedIterator, ExactSizeIterator, Iterator};

struct IterMut<'a, T> {
    pub inner: &'a mut [T],
}

impl<'a, T> Invariant for IterMut<'a, T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        // Property that is always true but we must carry around..
        pearlite! { (^self.inner)@.len() == (*self.inner)@.len() }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { resolve(self.inner) && self.inner@ == Seq::empty() }
    }

    #[logic(open, inline)]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        self.inner.to_mut_seq() == visited.concat(tl.inner.to_mut_seq())
    }

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {
        let _ = Seq::<Self::Item>::concat_empty;
    }

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        let _ = Seq::<Self::Item>::concat_assoc;
    }

    #[ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.split_off_first_mut()
    }

    #[ensures(result.0@ == self.inner@.len())]
    #[ensures(result.1 == Some(result.0))]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let l = self.inner.len();
        (l, Some(l))
    }
}

impl<'a, T> IterMut<'a, T> {
    #[ensures(result == self)]
    fn into_iter(self) -> Self {
        self
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    #[ensures(result@ == self.inner@.len())]
    fn len(&self) -> usize {
        self.inner.len()
    }

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    #[logic(open, inline)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        self.inner.to_mut_seq() == o.inner.to_mut_seq().concat(visited.reverse())
    }

    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.completed()
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {
        let _ = Seq::<Self::Item>::reverse_empty();
        let _ = Seq::<Self::Item>::concat_empty;
    }

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {
        let _ = ab.reverse_concat(bc);
        let _ = Seq::<Self::Item>::concat_assoc;
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

    #[ensures(match result {
        None => self.completed_back(),
        Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
    })]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.inner.split_off_last_mut()
    }
}

#[ensures(result.inner@ == v@)]
#[ensures((^result.inner)@ == (^v)@)]
#[ensures((^v)@.len() == v@.len())]
fn iter_mut<'a, T>(v: &'a mut Vec<T>) -> IterMut<'a, T> {
    IterMut { inner: &mut v[..] }
}

#[ensures((^v)@.len() == v@.len())]
#[ensures(forall<i> 0 <= i && i < v@.len() ==> (^v)[i]@ == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    let mut it = iter_mut(v).into_iter();
    let iter_old = snapshot! { it };
    let mut produced = snapshot! { Seq::empty() };
    #[invariant(iter_old.produces(produced.inner(), it))]
    #[invariant(forall<i> 0 <= i && i < produced.len() ==> (^produced[i])@ == 0)]
    loop {
        match it.next() {
            Some(x) => {
                produced = snapshot! { produced.concat(Seq::singleton(x)) };
                *x = 0;
            }
            None => break,
        }
    }
}
