#![feature(slice_take)]
extern crate creusot_contracts;

use creusot_contracts::*;

mod common;
use common::*;

struct IterMut<'a, T> {
    inner: &'a mut [T],
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() && (@self.inner).ext_eq(Seq::EMPTY) }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, tl: Self) -> bool {
        pearlite! {
            (@self.inner).len() == visited.len() + (@tl.inner).len() &&
            (@^self.inner).len() == visited.len() + (@^tl.inner).len() &&
            (@self.inner).subsequence(visited.len(), (@self.inner).len()).ext_eq(@tl.inner) &&
            (@^self.inner).subsequence(visited.len(), (@^self.inner).len()).ext_eq(@^tl.inner )&&
            (forall<i : Int> 0 <= i && i < visited.len() ==>
                (@self.inner)[i] == *visited[i] && (@^self.inner)[i] == ^visited[i])
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
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

#[ensures(@result.inner == @v)]
#[ensures(@^result.inner == @^v)]
#[ensures((@^v).len() == (@v).len())]
fn iter_mut<'a, T>(v: &'a mut Vec<T>) -> IterMut<'a, T> {
    IterMut { inner: &mut v[..] }
}

#[ensures((@^v).len() == (@v).len())]
#[ensures(forall<i : _> 0 <= i && i < (@v).len() ==> @(@^v)[i] == 0)]
pub fn all_zero(v: &mut Vec<usize>) {
    #[invariant(user, forall<i : Int> 0 <= i && i < produced.len() ==> @^produced[i] == 0)]
    for x in iter_mut(v) {
        *x = 0;
    }
}
