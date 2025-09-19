use crate::{
    std::iter::{DoubleEndedIterator, Iterator, Rev},
    *,
};

pub trait RevExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn iter_mut(&mut self) -> &mut I;
}

impl<I> RevExt<I> for Rev<I> {
    #[logic]
    #[trusted]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        dead
    }

    #[logic]
    #[trusted]
    #[ensures((*self).iter() == *result && (^self).iter() == ^result)]
    fn iter_mut(&mut self) -> &mut I {
        dead
    }
}

impl<I: DoubleEndedIterator> Iterator for Rev<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! { self.iter_mut().completed() }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.iter().produces_back(visited, o.iter())
        }
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
