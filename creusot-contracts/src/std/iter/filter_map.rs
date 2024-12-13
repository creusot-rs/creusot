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
    #[predicate(prophetic)]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! {
            // trivial precondition: simplification for sake of proof complexity
            forall<f: F, i: I::Item> f.precondition((i,)) &&
            // immutable state: simplification for sake of proof complexity
            (forall<f: F, g: F> f.unnest(g) ==> f == g) &&
            // precision of postcondition. This is not *necessary*, but simplifies the proof that we have returned *all* elements which evaluate to true.
            // If we remove this we could prove an alternate statement of produces that says we returned `true` for elements in `visited`, and `false` for
            // ones which we didn't remove. *if* the postcondition happened to be precise, these two statements would be equivalent .
            (forall<f1: F, f2: F, i: _> !((exists<b : B> f1.postcondition_mut((i,), f2, Some(b))) && f1.postcondition_mut((i,), f2, None)))
        }
    }
}

/// Asserts that `f` has no precondition: any closure state can be called with any input value
/// In a future release this restriction may be lifted or weakened
#[open]
#[predicate(prophetic)]
pub fn no_precondition<A, B, F: FnMut(A) -> Option<B>>(_: F) -> bool {
    pearlite! { forall<f : F, i : A> f.precondition((i,)) }
}

/// Asserts that the captures of `f` are used immutably
/// In a future release this restriction may be lifted or weakened
#[open]
#[predicate(prophetic)]
pub fn immutable<A, B, F: FnMut(A) -> Option<B>>(_: F) -> bool {
    pearlite! { forall<f : F, g : F> f.unnest(g) ==> f == g }
}

/// Asserts that the postcondition of `f` is *precise*: that there are never two possible values matching the postcondition
#[open]
#[predicate(prophetic)]
pub fn precise<A, B, F: FnMut(A) -> Option<B>>(_: F) -> bool {
    pearlite! { forall<f1 : F, f2 : F, i : _> !((exists<b: B> f1.postcondition_mut((i,), f2, Some(b))) && f1.postcondition_mut((i,), f2, None)) }
}

impl<I, B, F> Iterator for FilterMap<I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> Option<B>,
{
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (exists<s: Seq<_>, e : &mut I > self.iter().produces(s, *e) && e.completed() &&
                forall<i : _> 0 <= i && i < s.len() ==> (*self).func().postcondition_mut((s[i],), (^self).func(), None))
            && (*self).func() == (^self).func()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, succ: Self) -> bool {
        pearlite! {
            self.invariant() ==>
            self.func().unnest(succ.func()) &&
            // f here is a mapping from indices of `visited` to those of `s`, where `s` is the whole sequence produced by the underlying iterator
            // Interestingly, Z3 guesses `f` quite readily but gives up *totally* on `s`. However, the addition of the final assertions on the correctness of the values
            // blocks z3's guess for `f`.
            exists<s : Seq<I::Item>, f : Mapping<Int, Int>> self.iter().produces(s, succ.iter()) &&
                // `f` is a monotone mapping
                (forall<i : _, j :_ > 0 <= i && i <= j && j < visited.len() ==> 0 <= f.get(i) && f.get(i) <= f.get(j) && f.get(j) < s.len()) &&
                (forall<j : _> 0 <= j && j < visited.len() ==> self.func().postcondition_mut((s[f[j]],), self.func(), Some(visited[j]))) &&
                (forall<i : _> 0 <= i && i < s.len() ==> self.func().postcondition_mut((s[i],), self.func(), None) == !exists<j: Int> f[j] == i)
        }
    }

    #[law]
    #[open(self)]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
