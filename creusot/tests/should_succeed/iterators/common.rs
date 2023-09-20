// UISKIP WHY3SKIP
use creusot_contracts::{logic::Seq, *};

pub trait Iterator {
    type Item;

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, _o: Self) -> bool;

    #[predicate]
    fn completed(&mut self) -> bool;

    #[law]
    #[ensures(a.produces(Seq::EMPTY, a))]
    fn produces_refl(a: Self);

    #[law]
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
