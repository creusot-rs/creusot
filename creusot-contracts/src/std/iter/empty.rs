use crate::{invariant::*, std::iter::Empty, *};

impl<T> Iterator for Empty<T> {
    #[open]
    #[predicate(prophetic)]
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

extern_spec! {
    mod std {
        mod iter {
            impl<T> Iterator for Empty<T> {
                #[pure]
                #[ensures(result == None && self.completed())]
                fn next(&mut self) -> Option<T>;
            }
        }
    }
}
