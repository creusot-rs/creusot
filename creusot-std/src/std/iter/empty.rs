use crate::{prelude::*, std::iter::Empty};

impl<T> IteratorSpec for Empty<T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        resolve(self)
    }

    #[logic(open)]
    fn produces(self, visited: Seq<T>, o: Self) -> bool {
        pearlite! { visited == Seq::empty() && self == o }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {
        proof_assert!(Seq::<T>::empty().concat(Seq::empty()) == Seq::empty())
    }
}

extern_spec! {
    impl<T> Iterator for Empty<T> {
        #[check(ghost)]
        #[ensures(result == None && self.completed())]
        fn next(&mut self) -> Option<T>;
    }
}
