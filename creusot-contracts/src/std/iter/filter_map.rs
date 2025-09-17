use crate::{logic::Mapping, std::ops::*, *};
use ::std::iter::FilterMap;

pub trait FilterMapExt<I, F> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn func(self) -> F;
}

impl<I, F> FilterMapExt<I, F> for FilterMap<I, F> {
    #[trusted]
    #[logic]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        dead
    }

    #[trusted]
    #[logic]
    #[ensures(inv(self) ==> inv(result))]
    fn func(self) -> F {
        dead
    }
}

impl<B, I: Iterator, F: FnMut(I::Item) -> Option<B>> Invariant for FilterMap<I, F> {
    #[logic(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            // trivial precondition: simplification for sake of proof complexity
            no_precondition(self.func()) &&
            // immutable state: simplification for sake of proof complexity
            immutable(self.func()) &&
            // precision of postcondition
            precise(self.func())
        }
    }
}

/// Asserts that `f` has no precondition: any closure state can be called with any input value
/// In a future release this restriction may be lifted or weakened
#[logic(open, prophetic)]
pub fn no_precondition<A, B, F: FnMut(A) -> Option<B>>(f: F) -> bool {
    pearlite! { forall<i: A> f.precondition((i,)) }
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
    pearlite! { forall<f2: F, i> !((exists<b: B> f1.postcondition_mut((i,), f2, Some(b))) && f1.postcondition_mut((i,), f2, None)) }
}

impl<I, B, F> Iterator for FilterMap<I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> Option<B>,
{
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (exists<s: Seq<_>, e: &mut I > self.iter().produces(s, *e) && e.completed() &&
                forall<i> 0 <= i && i < s.len() ==> (*self).func().postcondition_mut((s[i],), (^self).func(), None))
            && (*self).func() == (^self).func()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.invariant() ==>
            self.func().hist_inv(succ.func()) &&
            // f here is a mapping from indices of `visited` to those of `s`, where `s` is the whole sequence produced by the underlying iterator
            // Interestingly, Z3 guesses `f` quite readily but gives up *totally* on `s`. However, the addition of the final assertions on the correctness of the values
            // blocks z3's guess for `f`.
            exists<s: Seq<I::Item>, f: Mapping<Int, Int>> self.iter().produces(s, succ.iter()) &&
                (forall<i> 0 <= i && i < visited.len() ==> 0 <= f.get(i) && f.get(i) < s.len()) &&
                // `f` is a monotone mapping
                (forall<i, j> 0 <= i && i < j && j < visited.len() ==> f.get(i) < f.get(j)) &&
                // `f` points to elements produced in `s` (by the underlying `iter`) for which the predicate `self.func()` returned `Some`.
                (forall<i> 0 <= i && i < visited.len() ==> self.func().postcondition_mut((s[f.get(i)],), self.func(), Some(visited[i]))) &&
                // For other elements not in the image of `f`, the predicate `self.func()` returned `None`.
                (forall<j> 0 <= j && j < s.len()
                    ==> (!exists<i> 0 <= i && i < visited.len() && f.get(i) == j) == self.func().postcondition_mut((s[j],), self.func(), None))
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
