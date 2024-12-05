use crate::{invariant::*, resolve::structural_resolve, std::iter::Cloned, *};

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
    #[predicate(prophetic)]
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
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<inner : &mut _> *inner == self.iter() && ^inner == (^self).iter() && inner.completed()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            exists<s: Seq<&'a T>>
                   self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i] == *s[i]
        }
    }

    #[law]
    #[open(self)]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
