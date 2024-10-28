use crate::{invariant::*, std::iter::Once, *};

impl<T> View for Once<T> {
    type ViewTy = Option<T>;

    #[logic]
    #[trusted]
    #[open(self)]
    fn view(self) -> Option<T> {
        pearlite! { absurd }
    }
}

impl<T> Iterator for Once<T> {
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> inv(e) && self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
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

extern_spec! {
    mod std {
        mod iter {
            impl<T> Iterator for Once<T> {
                #[pure]
                #[ensures(match result {
                    None => self.completed(),
                    Some(v) => (*self).produces(Seq::singleton(v), ^self)
                })]
                fn next(&mut self) -> Option<T>;
            }
        }
    }
}
