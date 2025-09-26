#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, std::iter::Take, *};

pub trait TakeExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn iter_mut(&mut self) -> &mut I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> TakeExt<I> for Take<I> {
    #[trusted]
    #[logic(opaque)]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        dead
    }

    #[trusted]
    #[logic(opaque)]
    #[ensures((*self).iter() == *result && (^self).iter() == ^result)]
    fn iter_mut(&mut self) -> &mut I {
        dead
    }

    #[trusted]
    #[logic(opaque)]
    #[ensures(result >= 0 && result <= usize::MAX@)]
    fn n(self) -> Int {
        dead
    }
}

impl<I> Resolve for Take<I> {
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

impl<I: Iterator> Iterator for Take<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.n() == 0 && resolve(self) ||
            (*self).n() > 0 && (*self).n() == (^self).n() + 1 && self.iter_mut().completed()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.n() == o.n() + visited.len() && self.iter().produces(visited, o.iter())
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
