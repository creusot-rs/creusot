use crate::{invariant::Invariant, std::iter::Once, *};

impl<T> ShallowModel for Once<T> {
    type ShallowModelTy = Option<T>;

    #[logic]
    #[trusted]
    fn shallow_model(self) -> Option<T> {
        pearlite! { absurd }
    }
}

impl<T> Invariant for Once<T> {}

impl<T> Iterator for Once<T> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { (*self)@ == None && self.resolve() }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            exists<e: Self::Item> self@ == Some(e) && visited == Seq::singleton(e) && o@ == None
        }
    }

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
