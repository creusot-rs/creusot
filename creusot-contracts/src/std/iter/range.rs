use crate as creusot_contracts;
use crate::{
    logic::{Int, Seq},
    std::{iter::Iterator, ops::RangeInclusiveExt},
    DeepModel, Invariant, Resolve,
};
use creusot_contracts_proc::*;
use std::{
    iter::Step,
    ops::{Range, RangeInclusive},
};

impl<Idx: DeepModel<DeepModelTy = Int> + Step> Iterator for Range<Idx> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.resolve() && self.start.deep_model() >= self.end.deep_model()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.end == o.end && self.start.deep_model() <= o.start.deep_model()
            && (visited.len() > 0 ==> o.start.deep_model() <= o.end.deep_model())
            && visited.len() == o.start.deep_model() - self.start.deep_model()
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                visited[i].deep_model() == self.start.deep_model() + i
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

impl<Idx: DeepModel<DeepModelTy = Int> + Step> Iterator for RangeInclusive<Idx> {
    #[predicate]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.is_empty_log() && (^self).is_empty_log()
        }
    }

    #[predicate]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            if self.is_empty_log() {
                o.is_empty_log() && visited == Seq::EMPTY
            } else {
                (if o.is_empty_log() {
                    visited.len() == self.end_log().deep_model() - self.start_log().deep_model() + 1
                } else {
                    o.end_log() == self.end_log() && self.start_log().deep_model() <= o.start_log().deep_model()
                    && visited.len() == o.start_log().deep_model() - self.start_log().deep_model()
                })
                && forall<i : Int> 0 <= i && i < visited.len() ==>
                    visited[i].deep_model() == self.start_log().deep_model() + i
            }
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
