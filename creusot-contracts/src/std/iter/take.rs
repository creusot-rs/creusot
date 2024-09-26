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
    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures((*self).iter() == *result && (^self).iter() == ^result)]
    fn iter_mut(&mut self) -> &mut I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result >= 0 && result <= usize::MAX@)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

#[trusted]
impl<I> Resolve for Take<I> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        pearlite! {
            resolve(&self.iter())
        }
    }
}

impl<I: Iterator> Iterator for Take<I> {
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.n() == 0 && resolve(&self) ||
            (*self).n() > 0 && (*self).n() == (^self).n() + 1 && self.iter_mut().completed()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.n() == o.n() + visited.len() && self.iter().produces(visited, o.iter())
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
