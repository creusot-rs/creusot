use crate::{std::iter::Iterator, *};

impl<'a> Iterator for ::std::str::Lines<'a> {
    #[trusted]
    #[predicate(prophetic)]
    fn produces(self, _visited: Seq<Self::Item>, _o: Self) -> bool {
        dead
    }

    #[trusted]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        dead
    }

    #[trusted]
    #[law]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[trusted]
    #[law]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
