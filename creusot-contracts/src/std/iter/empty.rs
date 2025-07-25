use crate::{std::iter::Empty, *};

impl<T> Iterator for Empty<T> {
    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.resolve() }
    }

    #[open]
    #[logic]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { visited == Seq::empty() && self == o }
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
