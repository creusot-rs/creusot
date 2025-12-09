use crate::{prelude::*, std::iter::Empty};

impl<T> IteratorSpec for Empty<T> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        resolve(self)
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! { visited == Seq::empty() && self == o }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

extern_spec! {
    mod core {
        mod iter {
            impl<T> Iterator for Empty<T> {
                #[check(ghost)]
                #[ensures(result == None && self.completed())]
                fn next(&mut self) -> Option<T>;
            }
        }
    }
}
