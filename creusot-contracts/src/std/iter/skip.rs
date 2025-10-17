#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{std::iter::Skip, *};

pub trait SkipExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> usize;
}

impl<I> SkipExt<I> for Skip<I> {
    #[logic(opaque)]
    fn iter(self) -> I {
        dead
    }

    #[logic(opaque)]
    fn n(self) -> usize {
        dead
    }
}

impl<I> Resolve for Skip<I> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        resolve(self.iter())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<I: Iterator> Invariant for Skip<I> {
    #[logic(prophetic, open, inline)]
    fn invariant(self) -> bool {
        inv(self.iter())
    }
}

impl<I: Iterator> Iterator for Skip<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (^self).n()@ == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I>
                   s.len() <= (*self).n()@
                && self.iter().produces(s, *i)
                && (forall<i> 0 <= i && i < s.len() ==> resolve(s[i]))
                && i.completed()
                && ^i == (^self).iter()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::empty() && self == o ||
            o.n()@ == 0 && visited.len() > 0 &&
            exists<s: Seq<Self::Item>>
                   s.len() == self.n()@
                && self.iter().produces(s.concat(visited), o.iter())
                && forall<i> 0 <= i && i < s.len() ==> resolve(s[i])
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
