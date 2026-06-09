// WHY3PROVE
extern crate creusot_std;
use creusot_std::{logic::Seq, prelude::*};

pub mod common;
use common::{ExactSizeIterator, Iterator};

pub struct Fuse<I: Iterator> {
    pub iter: Option<I>,
}

impl<I: Iterator> Iterator for Fuse<I> {
    type Item = I::Item;

    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            (self.iter == None || exists<it:&mut I> it.completed() && self.iter == Some(*it))
            && (^self).iter == None
        }
    }

    #[logic(open, prophetic)]
    fn produces(self, prod: Seq<Self::Item>, other: Self) -> bool {
        match self.iter {
            None => prod == Seq::empty() && other.iter == self.iter,
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

    #[logic(open, law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(open, law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[ensures(match self.iter {
        Some(s) => I::size_hint.postcondition((&s,), result),
        None => result == (0usize, Some(0usize))
    })]
    fn size_hint(&self) -> (usize, Option<usize>) {
        match self.iter {
            Some(ref iter) => iter.size_hint(),
            None => (0, Some(0)),
        }
    }
}

impl<I: ExactSizeIterator> ExactSizeIterator for Fuse<I> {
    #[logic(law)]
    #[ensures(forall<r> Self::size_hint.postcondition((&self,), r) ==> r.1 == Some(r.0))]
    fn size_is_exact(self) {
        let _ = I::size_is_exact;
    }
}

// Not a subtrait of `FusedIterator` here for type inference reasons.
// extern_spec! version should be though.
pub trait FusedIterator: Iterator {
    #[logic(law)]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::empty())]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self);
}

impl<I: Iterator> FusedIterator for Fuse<I> {
    #[logic(open, law)]
    #[requires(self.completed())]
    #[requires((^self).produces(steps, next))]
    #[ensures(steps == Seq::empty())]
    fn is_fused(&mut self, steps: Seq<Self::Item>, next: Self) {}
}
