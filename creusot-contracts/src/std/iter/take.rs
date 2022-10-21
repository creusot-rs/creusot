use crate::{invariant::Invariant, std::iter::Take, *};

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
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[ensures((*self).iter() == *result && (^self).iter() == ^result)]
    fn iter_mut(&mut self) -> &mut I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[ensures(result >= 0 && result <= @usize::MAX)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

#[trusted]
impl<I> Resolve for Take<I> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! {
            self.iter().resolve()
        }
    }
}

impl<I: Invariant> Invariant for Take<I> {
    #[predicate]
    fn invariant(self) -> bool {
        self.iter().invariant()
    }
}

impl<I: Iterator> Iterator for Take<I> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.n() == 0 && self.resolve() ||
            (*self).n() > 0 && (*self).n() == (^self).n() + 1 && self.iter_mut().completed()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.n() == o.n() + visited.len() && self.iter().produces(visited, o.iter())
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
