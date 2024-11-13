use crate::{invariant::*, resolve::structural_resolve, std::iter::Enumerate, *};

pub trait EnumerateExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> EnumerateExt<I> for Enumerate<I> {
    #[trusted]
    #[logic]
    #[ensures(inv(self) ==> inv(result))]
    fn iter(self) -> I {
        dead
    }

    #[trusted]
    #[logic]
    fn n(self) -> Int {
        dead
    }
}

impl<I> Resolve for Enumerate<I> {
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

impl<I: Iterator> Invariant for Enumerate<I> {
    #[open(self)]
    #[predicate(prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            (forall<s: Seq<I::Item>, i: I>
                #![trigger self.iter().produces(s, i)]
                inv(s) && inv(i) && self.iter().produces(s, i) ==>
                self.n() + s.len() < std::usize::MAX@)
            && (forall<i: &mut I> i.completed() ==> i.produces(Seq::EMPTY, ^i))
        }
    }
}

impl<I> Iterator for Enumerate<I>
where
    I: Iterator,
{
    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            exists<inner : &mut _> inv(inner)
                && *inner == self.iter()
                && ^inner == (^self).iter()
                && inner.completed()
                && self.n() == (^self).n()
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == o.n() - self.n()
            && exists<s: Seq<I::Item>> inv(s)
                && self.iter().produces(s, o.iter())
                && visited.len() == s.len()
                && forall<i: Int> 0 <= i && i < s.len() ==> visited[i].0@ == self.n() + i && visited[i].1 == s[i]
        }
    }

    #[law]
    #[open(self)]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open(self)]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
