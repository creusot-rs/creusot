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
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
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
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
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
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        self.iter().size_hint_exact(r)
    }
}
