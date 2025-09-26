extern crate creusot_contracts;
use creusot_contracts::{
    invariant::{Invariant, inv},
    logic::Seq,
    *,
};

mod common;
use common::Iterator;

#[derive(Resolve)]
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
        pearlite! { self.inner.resolve() && self.inner@.ext_eq(Seq::empty()) }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            self.inner@.len() == visited.len() + tl.inner@.len() &&
            (forall<i> 0 <= i && i < self.inner@.len() ==>
                *self.inner.to_mut_seq()[i] == *visited.concat(tl.inner.to_mut_seq())[i] &&
                ^self.inner.to_mut_seq()[i] == ^visited.concat(tl.inner.to_mut_seq())[i]
            )
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
        (self.inner).split_off_first_mut()
    }
}

impl<'a, T> IterMut<'a, T> {
    #[ensures(result == self)]
    fn into_iter(self) -> Self {
        self
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
    #[invariant(inv(it))]
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
