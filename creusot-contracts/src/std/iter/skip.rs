use crate::{invariant::Invariant, std::iter::Skip, *};

pub trait SkipExt<I> {
    #[logic]
    fn iter(self) -> I;

    #[logic]
    fn n(self) -> Int;
}

impl<I> SkipExt<I> for Skip<I> {
    #[logic]
    #[trusted]
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[logic]
    #[trusted]
    #[ensures(result >= 0 && result <= @usize::MAX)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

#[trusted]
impl<I> Resolve for Skip<I> {
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! {
            self.iter().resolve()
        }
    }
}

impl<I: Invariant> Invariant for Skip<I> {
    #[predicate]
    fn invariant(self) -> bool {
        self.iter().invariant()
    }
}

impl<I: Iterator> Iterator for Skip<I> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            (^self).n() == 0 &&
            exists<s: Seq<Self::Item>, i: &mut I>
                s.len() <= (*self).n() &&
                self.iter().produces(s, *i) &&
                (forall<i: Int> 0 <= i && i < s.len() ==> s[i].resolve()) &&
                i.completed() &&
                ^i == (^self).iter()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited == Seq::EMPTY && self == o ||
            o.n() == 0 && visited.len() > 0 &&
            exists<s: Seq<Self::Item>>
                s.len() == self.n() &&
                self.iter().produces(s.concat(visited), o.iter()) &&
                forall<i: Int> 0 <= i && i < s.len() ==> s[i].resolve()
        }
    }

    #[law]
    #[requires(a.invariant())]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self) {}

    #[law]
    #[requires(a.invariant())]
    #[requires(b.invariant())]
    #[requires(c.invariant())]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}
