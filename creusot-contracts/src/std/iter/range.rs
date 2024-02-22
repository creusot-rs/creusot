use crate::{
    std::{
        iter::Step,
        ops::{Range, RangeInclusive},
    },
    *,
};

impl<Idx: DeepModel<DeepModelTy = Int> + Step> Iterator for Range<Idx> {
    #[predicate]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.resolve() && self.start.deep_model() >= self.end.deep_model()
        }
    }

    #[predicate]
    #[open]
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

#[ghost]
#[open]
#[ensures(r.is_empty_log() == (result == 0))]
pub fn range_inclusive_len<Idx: DeepModel<DeepModelTy = Int>>(r: RangeInclusive<Idx>) -> Int {
    pearlite! {
        if r.is_empty_log() { 0 }
        else { r.end_log().deep_model() - r.start_log().deep_model() + 1 }
    }
}

impl<Idx: DeepModel<DeepModelTy = Int> + Step> Iterator for RangeInclusive<Idx> {
    #[predicate]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.is_empty_log() && (^self).is_empty_log()
        }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == range_inclusive_len(self) - range_inclusive_len(o) &&
            (self.is_empty_log() ==> o.is_empty_log()) &&
            (o.is_empty_log() || self.end_log() == o.end_log()) &&
            forall<i : Int> 0 <= i && i < visited.len() ==>
                visited[i].deep_model() == self.start_log().deep_model() + i
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
