use crate::{inv, logic::*, macros::*, std::ops::*, Invariant, Iterator};
use std::iter::Filter;

pub trait FilterExt<I, F> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn func(self) -> F;

    #[logic]
    fn func_mut(&mut self) -> &mut F;
}

impl<I, F> FilterExt<I, F> for Filter<I, F> {
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

    #[trusted]
    #[logic]
    #[ensures(inv(self) ==> inv(result))]
    #[ensures((*self).func() == *result && (^self).func() == ^result)]
    fn func_mut(&mut self) -> &mut F {
        dead
    }
}

impl<I: Iterator, F: FnMut(&I::Item) -> bool> Invariant for Filter<I, F> {
    #[predicate(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            // trivial precondition: simplification for sake of proof complexity
            forall<f : F, i : &I::Item> f.precondition((i,)) &&
            // immutable state: simplification for sake of proof complexity
            (forall<f : F, g : F> f.unnest(g) ==> f == g) &&
            // plain-ness: this is a simplification as well, but a fairly major one for very minor loss of expressivity. In short all it says
            // is that we cannot `a == b` two mutable borrows.
            (forall<f : &mut F, g : &mut F, i :_, b :_> *f == *g && ^f == ^g ==> f.postcondition_mut((i,), b) == g.postcondition_mut((i,), b)) &&
            // precision of postcondition. This is not *necessary*, but simplifies the proof that we have returned *all* elements which evaluate to true.
            // If we remove this we could prove an alternate statement of produces that says we returned `true` for elements in `visited`, and `false` for
            // ones which we didn't remove. *if* the postcondition happened to be precise, these two statements would be equivalent .
            (forall<f : &mut F, i : _> !(f.postcondition_mut((i,), true) && f.postcondition_mut((i,), false)))
        }
    }
}

/// Asserts that `f` has no precondition: any closure state can be called with any input value
/// In a future release this restriction may be lifted or weakened
#[open]
#[predicate]
pub fn no_precondition<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f : F, i : A> f.precondition((i,)) }
}

/// Asserts that the captures of `f` are used immutably
/// In a future release this restriction may be lifted or weakened
#[open]
#[predicate]
pub fn immutable<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f : F, g : F> f.unnest(g) ==> f == g }
}

/// The postcondition of `f` does not depend on prophecies storied in its in environment.
/// In practice this means that the postcondition is not testing the equality of a mutable borrow
#[open]
#[predicate(prophetic)]
pub fn plain<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f : &mut F, g : &mut F, i :_, b :_> *f == *g && ^f == ^g ==> f.postcondition_mut((i,), b) == g.postcondition_mut((i,), b) }
}

/// Asserts that the postcondition of `f` is *precise*: that there are never two possible values matching the postcondition
#[open]
#[predicate]
pub fn precise<A, F: FnMut(A) -> bool>(_: F) -> bool {
    pearlite! { forall<f : &mut F, i : _> !(f.postcondition_mut((i,), true) && f.postcondition_mut((i,), false)) }
}

impl<I, F> Iterator for Filter<I, F>
where
    I: Iterator,
    F: FnMut(&I::Item) -> bool,
{
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (exists<s: Seq<_>, e : &mut I > self.iter().produces(s, *e) && e.completed() &&
                forall<i : _> 0 <= i && i < s.len() ==> self.func_mut().postcondition_mut((&s[i],), false))
            && (*self).func() == (^self).func()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.func().unnest(succ.func()) &&
            // f here is a mapping from indices of `visited` to those of `s`, where `s` is the whole sequence produced by the underlying iterator
            // Interestingly, Z3 guesses `f` quite readily but gives up *totally* on `s`. However, the addition of the final assertions on the correctness of the values
            // blocks z3's guess for `f`.
            exists<s : Seq<Self::Item>, f : Mapping<Int, Int>> self.iter().produces(s, succ.iter()) &&
                // `f` is a monotone mapping
                (forall<i : _, j :_ > 0 <= i && i <= j && j < visited.len() ==> 0 <= f.get(i) && f.get(i) <= f.get(j) && f.get(j) < s.len()) &&
                (forall<i : _, > 0 <= i && i < visited.len() ==> visited[i] == s[f.get(i)]) &&

                (forall<bor_f : &mut F, i : _> *bor_f == self.func() && ^bor_f == self.func() ==>
                    0 <= i &&  i < s.len() ==>  (exists<j : _> 0 <= j && j < visited.len() && f.get(j) == i) == bor_f.postcondition_mut((&s[i],), true)
                )
        }
    }

    #[law]
    #[open(self)]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
