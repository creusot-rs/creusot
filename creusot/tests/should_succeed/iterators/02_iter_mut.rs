#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::{
    invariant::{inv, Invariant},
    logic::{Int, Seq},
    *,
};

mod common;
use common::Iterator;

struct IterMut<'a, T> {
    inner: &'a mut [T],
}

impl<'a, T> Invariant for IterMut<'a, T> {
    #[open]
    #[predicate]
    fn invariant(self) -> bool {
        // Property that is always true but we must carry around..
        pearlite! { (^self.inner)@.len() == (*self.inner)@.len() }
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && self.inner@.ext_eq(Seq::EMPTY) }
    }

    #[open]
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        self.inner.to_mut_seq().ext_eq(visited.concat(tl.inner.to_mut_seq()))
    }

    #[law]
    #[open]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        (self.inner).take_first_mut()
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
#[ensures(forall<i : _> 0 <= i && i < v@.len() ==> (^v)[i]@ == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    let mut it = iter_mut(v).into_iter();
    let iter_old = ghost! { it };
    let mut produced = ghost! { Seq::EMPTY };
    #[invariant(inv(it))]
    #[invariant(iter_old.produces(produced.inner(), it))]
    #[invariant(forall<i : Int> 0 <= i && i < produced.len() ==> (^produced[i])@ == 0)]
    loop {
        match it.next() {
            Some(x) => {
                produced = ghost! { produced.concat(Seq::singleton(x)) };
                *x = 0;
            }
            None => break,
        }
    }
}
