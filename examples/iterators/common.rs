// UISKIP WHY3SKIP
use creusot_std::{logic::Seq, prelude::*};

pub trait Iterator {
    type Item;

    #[logic(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[logic(prophetic)]
    fn completed(&mut self) -> bool;

    #[logic(law, prophetic)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self);

    #[logic(law, prophetic)]
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
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(r.1 == Some(r.0))]
    #[allow(unused_variables)]
    fn size_hint_exact(&self, r: (usize, Option<usize>));

    #[ensures(Self::size_hint.postcondition((self,), (result, Some(result))))]
    fn len(&self) -> usize {
        snapshot!(Self::size_hint_exact);
        let (lower, upper) = self.size_hint();
        assert_eq!(upper, Some(lower));
        lower
    }

    #[ensures(exists<l> Self::size_hint.postcondition((self,), (l, Some(l))) && result == (l == 0usize))]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

pub trait DoubleEndedIterator: Iterator {
    #[logic(prophetic)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[logic(prophetic)]
    fn completed_back(&mut self) -> bool;

    #[logic(law, prophetic)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self);

    #[logic(law, prophetic)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);

    #[logic(law, prophetic)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>));

    #[ensures(match result {
        None => self.completed_back(),
        Some(v) => (*self).produces_back(Seq::singleton(v), ^self)
    })]
    fn next_back(&mut self) -> Option<Self::Item>;
}
