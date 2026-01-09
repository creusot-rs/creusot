#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, prelude::*};
use core::iter::Copied;

pub trait CopiedExt<I> {
    #[logic]
    fn iter(self) -> I;
}

impl<I> CopiedExt<I> for Copied<I> {
    #[logic(opaque)]
    fn iter(self) -> I {
        dead
    }
}

impl<I> Invariant for Copied<I> {
    #[logic(prophetic, open, inline)]
    fn invariant(self) -> bool {
        inv(self.iter())
    }
}

impl<I> Resolve for Copied<I> {
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

impl<'a, I, T: 'a> IteratorSpec for Copied<I>
where
    I: IteratorSpec<Item = &'a T>,
    T: Copy,
{
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<inner: &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed()
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>>
                   self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> visited[i] == *s[i]
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
