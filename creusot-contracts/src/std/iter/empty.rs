use crate::{invariant::Invariant, std::iter::Empty, *};

impl<T> Invariant for Empty<T> {}

impl<T> Iterator for Empty<T> {
    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() }
    }

    #[open]
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { visited == Seq::EMPTY && self == o }
    }

    #[law]
    #[open(self)]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
