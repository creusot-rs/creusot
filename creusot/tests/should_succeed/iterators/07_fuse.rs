extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

mod common;
use common::Iterator;

pub struct Fuse<I: Iterator> {
    iter: Option<I>,
}

impl<I: Iterator> Iterator for Fuse<I> {
    type Item = I::Item;

    #[open]
    #[predicate(prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (self.iter == None || exists<it:&mut I> it.completed() && self.iter == Some(*it))
            && (^self).iter == None
        }
    }

    #[open]
    #[predicate(prophetic)]
    fn produces(self, prod: Seq<Self::Item>, other: Self) -> bool {
        match self.iter {
            None => prod == Seq::EMPTY && other.iter == self.iter,
            Some(i) => match other.iter {
                Some(i2) => i.produces(prod, i2),
                None => false,
            },
        }
    }

    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            None => None,
            Some(iter) => match iter.next() {
                None => {
                    self.iter = None;
                    None
                }
                x => x,
            },
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

// Not a subtrait of `FusedIterator` here for type inference reasons.
// extern_spec! version should be though.
pub trait FusedIterator: Iterator {
    #[law]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::EMPTY && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self);
}

impl<I: Iterator> FusedIterator for Fuse<I> {
    #[law]
    #[open]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::EMPTY && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self) {}
}
