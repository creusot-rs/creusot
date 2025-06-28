use crate::{std::iter::Repeat, *};

impl<T> View for Repeat<T> {
    type ViewTy = T;

    #[logic]
    #[trusted]
    fn view(self) -> T {
        dead
    }
}

impl<T: Clone> Iterator for Repeat<T> {
    #[open]
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { false }
    }

    #[open]
    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self == o &&
            forall<i> 0 <= i && i < visited.len() ==> T::clone.postcondition((&self@,), visited[i])
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
