use crate::{
    std::iter::{IntoIterator, Iterator},
    *,
};

impl<T, const N: usize> Iterator for ::std::array::IntoIter<T, N> {
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

impl<T, const N: usize> IntoIterator for [T; N] {
    #[predicate]
    #[open]
    fn into_iter_pre(self) -> bool {
        pearlite! { true }
    }

    #[trusted]
    #[predicate(prophetic)]
    fn into_iter_post(self, _res: Self::IntoIter) -> bool {
        dead
    }
}
