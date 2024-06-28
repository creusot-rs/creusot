use crate::{
    std::{
        iter::Step,
        ops::{Range, RangeInclusive},
    },
    *,
};

impl<Idx: EqModel<EqModelTy = Int> + Step> Iterator for Range<Idx> {
    #[predicate(prophetic)]
    #[open]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.resolve() && self.start.eq_model() >= self.end.eq_model()
        }
    }

    #[predicate]
    #[open]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.end == o.end && self.start.eq_model() <= o.start.eq_model()
            && (visited.len() > 0 ==> o.start.eq_model() <= o.end.eq_model())
            && visited.len() == o.start.eq_model() - self.start.eq_model()
            && forall<i : Int> 0 <= i && i < visited.len() ==>
                visited[i].eq_model() == self.start.eq_model() + i
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

#[logic]
#[open]
#[ensures(r.is_empty_log() == (result == 0))]
pub fn range_inclusive_len<Idx: EqModel<EqModelTy = Int>>(r: RangeInclusive<Idx>) -> Int {
    pearlite! {
        if r.is_empty_log() { 0 }
        else { r.end_log().eq_model() - r.start_log().eq_model() + 1 }
    }
}

impl<Idx: EqModel<EqModelTy = Int> + Step> Iterator for RangeInclusive<Idx> {
    #[predicate(prophetic)]
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
                visited[i].eq_model() == self.start_log().eq_model() + i
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
