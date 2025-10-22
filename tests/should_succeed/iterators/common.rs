// UISKIP WHY3SKIP
use creusot_contracts::{logic::Seq, prelude::*};

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
}
