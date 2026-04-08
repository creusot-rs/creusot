use crate::{invariant::*, prelude::*, std::iter::Enumerate};
#[cfg(creusot)]
use crate::{mode::Mode, resolve::structural_resolve};

pub trait EnumerateExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> usize;
}

impl<I> EnumerateExt<I> for Enumerate<I> {
    #[logic(opaque)]
    fn iter(self) -> I {
        dead
    }

    #[logic(opaque)]
    fn n(self) -> usize {
        dead
    }
}

impl<I> Resolve for Enumerate<I> {
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

impl<I: IteratorSpec> Invariant for Enumerate<I> {
    #[logic(prophetic)]
    #[ensures(result ==> inv(self.iter()))]
    fn invariant(self) -> bool {
        pearlite! {
            inv(self.iter())
            && (forall<s: Seq<I::Item>, i: I, mode: Mode>
                #[trigger(self.iter().produces(mode, s, i))]
                self.iter().produces(mode, s, i) ==>
                self.n()@ + s.len() < core::usize::MAX@)
            && (forall<i: &mut I> i.completed() ==> forall<mode: Mode> (*i).produces(mode, Seq::empty(), ^i))
        }
    }
}

impl<I: IteratorSpec> IteratorSpec for Enumerate<I> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<inner: &mut _> *inner == self.iter() && ^inner == (^self).iter()
                && inner.completed()
                && self.n()@ == (^self).n()@
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, mode: Mode, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.n()@ - self.n()@
            && exists<s: Seq<I::Item>>
                   self.iter().produces(mode, s, o.iter())
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> visited[i].0@ == self.n()@ + i && visited[i].1 == s[i]
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
