// UISKIP WHY3SKIP
use creusot_contracts::{invariant::inv, logic::Seq, *};

pub trait Iterator {
    type Item;

    #[predicate(prophetic)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool;

    #[predicate(prophetic)]
    fn completed(&mut self) -> bool;

    #[law]
    #[requires(inv(self))]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self);

    #[law]
    #[requires(inv(a))]
    #[requires(inv(b))]
    #[requires(inv(c))]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self);

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item>;
}
