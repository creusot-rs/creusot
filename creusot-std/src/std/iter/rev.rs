use crate::{
    prelude::*,
    std::iter::{ExactSizeIteratorSpec, Rev},
};

pub trait RevExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn iter_mut(&mut self) -> &mut I;
}

impl<I> RevExt<I> for Rev<I> {
    #[logic(opaque)]
    fn iter(self) -> I {
        dead
    }

    #[trusted]
    #[logic(opaque)]
    #[ensures((*self).iter() == *result && (^self).iter() == ^result)]
    fn iter_mut(&mut self) -> &mut I {
        dead
    }
}

impl<I> Invariant for Rev<I> {
    #[logic(prophetic, open, inline)]
    fn invariant(self) -> bool {
        inv(self.iter())
    }
}

impl<I: DoubleEndedIteratorSpec> IteratorSpec for Rev<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        self.iter_mut().completed_back()
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        self.iter().produces_back(visited, o.iter())
    }

    #[logic(law)]
    fn produces_refl(self) {}

    #[logic(law)]
    #[allow(unused_variables)]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

impl<I: DoubleEndedIteratorSpec> DoubleEndedIteratorSpec for Rev<I> {
    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.iter_mut().completed()
    }

    #[logic(open, prophetic)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        self.iter().produces(visited, o.iter())
    }

    #[logic(law)]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[allow(unused_variables)]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(law)]
    #[allow(unused_variables)]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}
}

extern_spec! {
    impl<I: DoubleEndedIterator> Iterator for Rev<I> {
        #[ensures(I::size_hint.postcondition((&self.iter(),), result))]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

impl<I: ExactSizeIteratorSpec + DoubleEndedIteratorSpec> ExactSizeIteratorSpec for Rev<I> {
    #[logic(law)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        self.iter().size_hint_exact(r)
    }
}
