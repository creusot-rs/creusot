#[cfg(creusot)]
use crate::mode::Mode;
use crate::{
    prelude::*,
    std::iter::{Empty, ExactSizeIteratorSpec},
};

impl<T> IteratorSpec for Empty<T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        resolve(self)
    }

    #[logic(open)]
    fn produces(self, _: Mode, visited: Seq<T>, o: Self) -> bool {
        pearlite! { visited == Seq::empty() && self == o }
    }

    #[logic(law)]
    #[ensures(forall<mode: Mode> self.produces(mode, Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(mode, ab, b))]
    #[requires(b.produces(mode, bc, c))]
    #[ensures(a.produces(mode, ab.concat(bc), c))]
    fn produces_trans(mode: Mode, a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {
        proof_assert!(Seq::<T>::empty().concat(Seq::empty()) == Seq::empty())
    }
}

extern_spec! {
    impl<T> Iterator for Empty<T> {
        #[check(ghost)]
        #[ensures(result == None && self.completed())]
        fn next(&mut self) -> Option<T>;

        #[check(ghost)]
        #[ensures(result == (0usize, Some(0usize)))]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

impl<T> ExactSizeIteratorSpec for Empty<T> {
    #[logic(law)]
    #[requires(exists<mode: Mode> Self::size_hint.postcondition(mode, (self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
}
