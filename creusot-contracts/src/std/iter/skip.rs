#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{std::iter::Skip, *};

pub trait SkipExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> SkipExt<I> for Skip<I> {
    #[logic]
    #[trusted]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        dead
    }

    #[logic]
    #[trusted]
    #[ensures(result >= 0 && result <= usize::MAX@)]
    fn n(self) -> Int {
        dead
    }
}

impl<I> Resolve for Skip<I> {
    #[open]
    #[logic(prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            resolve(self.iter())
        }
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<I: Iterator> Iterator for Skip<I> {
    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (^self).n() == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I>
                   s.len() <= (*self).n()
                && self.iter().produces(s, *i)
                && (forall<i> 0 <= i && i < s.len() ==> resolve(s[i]))
                && i.completed()
                && ^i == (^self).iter()
        }
    }

    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            o.n() == 0 && visited.len() > 0 &&
            exists<s: Seq<Self::Item>>
                   s.len() == self.n()
                && self.iter().produces(s.concat(visited), o.iter())
                && forall<i> 0 <= i && i < s.len() ==> resolve(s[i])
        }
    }

    #[law]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
