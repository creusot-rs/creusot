use crate::{std::iter::Skip, *};

pub trait SkipExt<I> {
    #[ghost]
    fn iter(self) -> I;

    #[ghost]
    fn n(self) -> Int;
}

impl<I> SkipExt<I> for Skip<I> {
    #[ghost]
    #[open(self)]
    #[trusted]
    fn iter(self) -> I {
        pearlite! { absurd }
    }

    #[ghost]
    #[open(self)]
    #[trusted]
    #[ensures(result >= 0 && result <= usize::MAX@)]
    fn n(self) -> Int {
        pearlite! { absurd }
    }
}

#[trusted]
impl<I> Resolve for Skip<I> {
    #[open]
    #[predicate]
    fn resolve(self) -> bool {
        pearlite! {
            self.iter().resolve()
        }
    }
}

impl<I: Iterator> Iterator for Skip<I> {
    #[open]
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

    #[open]
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
