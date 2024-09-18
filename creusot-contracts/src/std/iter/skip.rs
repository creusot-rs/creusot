use crate::{invariant::*, resolve::structural_resolve, std::iter::Skip, *};

pub trait SkipExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> SkipExt<I> for Skip<I> {
    #[logic]
    #[open(self)]
    #[trusted]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[logic]
    #[open(self)]
    #[trusted]
    #[ensures(result >= 0 && result <= usize::MAX@)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

impl<I> Resolve for Skip<I> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            resolve(&self.iter())
        }
    }

    #[trusted]
    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(&self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self)
    where
        Self: Sized,
    {
    }
}

impl<I: Iterator> Iterator for Skip<I> {
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (^self).n() == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I> inv(s) && inv(i)
                && s.len() <= (*self).n()
                && self.iter().produces(s, *i)
                && (forall<i: Int> 0 <= i && i < s.len() ==> resolve(&s[i]))
                && i.completed()
                && ^i == (^self).iter()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            o.n() == 0 && visited.len() > 0 &&
            exists<s: Seq<Self::Item>> inv(s)
                && s.len() == self.n()
                && self.iter().produces(s.concat(visited), o.iter())
                && forall<i: Int> 0 <= i && i < s.len() ==> resolve(&s[i])
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
