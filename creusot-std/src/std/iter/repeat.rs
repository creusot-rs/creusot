#[cfg(creusot)]
use crate::mode::Mode;
use crate::{prelude::*, std::iter::Repeat};

impl<T> View for Repeat<T> {
    type ViewTy = T;

    #[logic(opaque)]
    fn view(self) -> T {
        dead
    }
}

impl<T: Clone> IteratorSpec for Repeat<T> {
    #[logic(open)]
    fn completed(&mut self) -> bool {
        pearlite! { false }
    }

    #[logic(open)]
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self == o &&
            forall<i> 0 <= i && i < visited.len() ==> T::clone.postcondition(mode, (&self@,), visited[i])
        }
    }

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(
        mode: Mode,
        a: Self,
        ab: Seq<Self::Item>,
        b: Self,
        bc: Seq<Self::Item>,
        c: Self,
    ) {
    }
}
