extern crate creusot_contracts;
use creusot_contracts::{logic::Seq, *};

mod common;
use common::Iterator;

pub struct Fuse<I> {
    // Either it's an actual iterator or
    // it's the ghost of the last iterator *spooky*
    iter: Result<I, Ghost<I>>,
}

impl<I> Fuse<I> {
    #[logic]
    fn inner(self) -> I {
        match self.iter {
            Ok(i) => i,
            Err(gi) => *gi,
        }
    }
}

impl<I: Iterator> Iterator for Fuse<I> {
    type Item = I::Item;

    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! { exists<x :_> (^self).iter == Err(x) }
    }

    #[predicate]
    fn produces(self, prod: Seq<Self::Item>, other: Self) -> bool {
        match self.iter {
            Err(_) => prod == Seq::EMPTY && other.iter == self.iter,
            Ok(i) => i.produces(prod, other.inner()),
        }
    }

    #[predicate]
    fn invariant(self) -> bool {
        match self.iter {
            Ok(i) => i.invariant(),
            Err(gi) => gi.invariant(),
        }
    }

    #[maintains((mut self).invariant())]
    #[ensures(match result {
      None => self.completed(),
      Some(v) => (*self).produces(Seq::singleton(v), ^self)
    })]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.iter {
            Err(_) => None,
            Ok(iter) => match iter.next() {
                None => {
                    self.iter = Err(ghost! { *iter });
                    None
                }
                x => x,
            },
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
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::EMPTY && ^self == next)]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self) {}
}
