// UISKIP WHY3SKIP
use creusot_std::{logic::Seq, prelude::*};

pub trait Iterator {
    type Item;

    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[logic(prophetic)]
    fn completed(&mut self) -> bool;

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self);

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);

    #[ensures(match result {
        None => self.completed(),
        Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item>;

    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces(s, *i) && i.completed() ==> result.0@ <= s.len())]
    #[ensures(match result.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint(&self) -> (usize, Option<usize>);
}

pub trait ExactSizeIterator: Iterator {
    #[logic(law)]
    #[ensures(forall<r> Self::size_hint.postcondition((&self,), r) ==> r.1 == Some(r.0))]
    fn size_is_exact(self);

    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces(s, *i) && i.completed() ==> result@ == s.len())]
    #[ensures(forall<s: Seq<Self::Item>, i: Self>
        self.produces(s, i) ==> s.len() <= result@)]
    fn len(&self) -> usize {
        snapshot!(self.size_is_exact());
        let (lower, upper) = self.size_hint();
        assert_eq!(upper, Some(lower));
        lower
    }

    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces(s, *i) && i.completed() ==> result == (s == Seq::empty()))]
    #[ensures(forall<s: Seq<Self::Item>, i: Self>
        self.produces(s, i) && result ==> s == Seq::empty())]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
