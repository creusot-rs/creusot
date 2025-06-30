#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{invariant::*, std::iter::Cloned, *};

pub trait ClonedExt<I> {
    #[logic]
    fn iter(self) -> I;
}

impl<I> ClonedExt<I> for Cloned<I> {
    #[logic]
    #[trusted]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        dead
    }
}

impl<I> Resolve for Cloned<I> {
    #[open]
    #[logic(prophetic)]
    fn resolve(self) -> bool {
        resolve(&self.iter())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<'a, I, T: 'a> Iterator for Cloned<I>
where
    I: Iterator<Item = &'a T>,
    T: Clone,
{
    #[open]
    #[logic(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<inner: &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed()
        }
    }

    #[open]
    #[logic(prophetic)]
    fn produces(self, visited: Seq<T>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>>
                   self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i> 0 <= i && i < s.len() ==> T::clone.postcondition((s[i],), visited[i])
        }
    }

    #[law]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<T>, b: Self, bc: Seq<T>, c: Self) {}
}
