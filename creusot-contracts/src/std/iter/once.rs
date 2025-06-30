use crate::{std::iter::Once, *};

impl<T> View for Once<T> {
    type ViewTy = Option<T>;

    #[logic]
    #[trusted]
    fn view(self) -> Option<T> {
        dead
    }
}

impl<T> Iterator for Once<T> {
    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[law]
    #[ensures(self.produces(Seq::EMPTY, self))]
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
