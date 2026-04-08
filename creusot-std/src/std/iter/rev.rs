#[cfg(creusot)]
use crate::mode::Mode;
use crate::{prelude::*, std::iter::Rev};

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
        pearlite! { self.iter_mut().completed() }
    }

    #[logic(open, prophetic)]
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.iter().produces_back(mode, visited, o.iter())
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
