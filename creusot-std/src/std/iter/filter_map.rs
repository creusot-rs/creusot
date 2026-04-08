use crate::prelude::*;
#[cfg(creusot)]
use crate::{logic::Mapping, mode::Mode, std::ops::*};
use core::iter::FilterMap;

pub trait FilterMapExt<I, F> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn func(self) -> F;
}

impl<I, F> FilterMapExt<I, F> for FilterMap<I, F> {
    #[logic(opaque)]
    fn iter(self) -> I {
        dead
    }

    #[logic(opaque)]
    fn func(self) -> F {
        dead
    }
}

impl<B, I: Iterator, F: FnMut(I::Item) -> Option<B>> Invariant for FilterMap<I, F> {
    #[logic(prophetic, open, inline)]
    fn invariant(self) -> bool {
        inv(self.iter()) && inv(self.func()) && private_invariant(self)
    }
}

#[logic(prophetic)]
pub fn private_invariant<B, I: Iterator, F: FnMut(I::Item) -> Option<B>>(
    f: FilterMap<I, F>,
) -> bool {
    // trivial precondition: simplification for sake of proof complexity
    no_precondition(f.func()) &&
    // immutable state: simplification for sake of proof complexity
    immutable(f.func()) &&
    // precision of postcondition
    precise(f.func())
}

/// Asserts that `f` has no precondition: any closure state can be called with any input value
/// In a future release this restriction may be lifted or weakened
#[logic(open, prophetic)]
pub fn no_precondition<A, B, F: FnMut(A) -> Option<B>>(f: F) -> bool {
    pearlite! { forall<mode: Mode, i: A> !mode.terminates() && inv(i) ==> f.precondition(mode, (i,)) }
}

/// Asserts that the captures of `f` are used immutably
/// In a future release this restriction may be lifted or weakened
#[logic(open, prophetic)]
pub fn immutable<A, B, F: FnMut(A) -> Option<B>>(f: F) -> bool {
    pearlite! { forall<g: F> f.hist_inv(g) ==> f == g }
}

/// Asserts that the postcondition of `f` is *precise*: that there are never two possible values matching the postcondition
#[logic(open, prophetic)]
pub fn precise<A, B, F: FnMut(A) -> Option<B>>(f1: F) -> bool {
    pearlite! { forall<mode: Mode, f2: F, i> !mode.terminates()
    ==> !((exists<b: B> f1.postcondition_mut(mode, (i,), f2, Some(b))) && f1.postcondition_mut(mode, (i,), f2, None)) }
}

impl<I: IteratorSpec, B, F: FnMut(I::Item) -> Option<B>> IteratorSpec for FilterMap<I, F> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            forall<mode: Mode>
            (exists<s: Seq<_>, e: &mut I > self.iter().produces(mode, s, *e) && e.completed() &&
                forall<i> 0 <= i && i < s.len() ==> (*self).func().postcondition_mut(mode, (s[i],), (^self).func(), None))
            && (*self).func() == (^self).func()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            private_invariant(self) ==>
            self.func().hist_inv(succ.func()) &&
            // f here is a mapping from indices of `visited` to those of `s`, where `s` is the whole sequence produced by the underlying iterator
            // Interestingly, Z3 guesses `f` quite readily but gives up *totally* on `s`. However, the addition of the final assertions on the correctness of the values
            // blocks z3's guess for `f`.
            exists<s: Seq<I::Item>, f: Mapping<Int, Int>> self.iter().produces(mode, s, succ.iter()) &&
                (forall<i> 0 <= i && i < visited.len() ==> 0 <= f.get(i) && f.get(i) < s.len()) &&
                // `f` is a monotone mapping
                (forall<i, j> 0 <= i && i < j && j < visited.len() ==> f.get(i) < f.get(j)) &&
                // `f` points to elements produced in `s` (by the underlying `iter`) for which the predicate `self.func()` returned `Some`.
                (forall<i> 0 <= i && i < visited.len() ==> self.func().postcondition_mut(mode, (s[f.get(i)],), self.func(), Some(visited[i]))) &&
                // For other elements not in the image of `f`, the predicate `self.func()` returned `None`.
                (forall<j> 0 <= j && j < s.len()
                    ==> (!exists<i> 0 <= i && i < visited.len() && f.get(i) == j) == self.func().postcondition_mut(mode, (s[j],), self.func(), None))
        }
    }

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
    }
}
