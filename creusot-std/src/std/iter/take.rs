#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, prelude::*, std::iter::ExactSizeIteratorSpec};
use core::iter::Take;

pub trait TakeExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn iter_mut(&mut self) -> &mut I;

    #[logic]
    fn n(self) -> usize;
}

impl<I> TakeExt<I> for Take<I> {
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

    #[logic(opaque)]
    fn n(self) -> usize {
        dead
    }
}

impl<I: Iterator> Invariant for Take<I> {
    #[logic(prophetic, open, inline)]
    fn invariant(self) -> bool {
        inv(self.iter())
    }
}

impl<I> Resolve for Take<I> {
    #[logic(open, prophetic, inline)]
    fn resolve(self) -> bool {
        resolve(self.iter())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<I: IteratorSpec> IteratorSpec for Take<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.n()@ == 0 && resolve(self) ||
            (*self).n()@ > 0 && (*self).n()@ == (^self).n()@ + 1 && self.iter_mut().completed()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.n()@ == o.n()@ + visited.len() && self.iter().produces(visited, o.iter())
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

extern_spec! {
    impl<I: Iterator> Iterator for Take<I> {
        #[ensures(self.n() > 0usize ==> exists<r>
            I::size_hint.postcondition((&self.iter(),), r) &&
            (r.0 <= self.n() ==> result.0 == r.0) &&
            (r.0 >= self.n() ==> result.0 == self.n()) &&
            match r.1 {
                Some(ub) =>
                    (ub <= self.n() ==> result.1 == Some(ub)) &&
                    (ub >= self.n() ==> result.1 == Some(self.n())),
                None => result.1 == Some(self.n()),
            }
        )]
        #[ensures(self.n() == 0usize ==> result == (0usize, Some(0usize)))]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

impl<I: ExactSizeIteratorSpec> ExactSizeIteratorSpec for Take<I> {
    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>)) {
        let _ = I::size_hint_exact;
    }
}
