use crate::{
    std::{
        iter::DoubleEndedIterator,
        ops::{Range, RangeInclusive},
    },
    *,
};
#[cfg(feature = "nightly")]
use ::std::iter::Step;

#[cfg(feature = "nightly")]
impl<Idx: DeepModel<DeepModelTy = Int> + Step> Iterator for Range<Idx> {
    #[predicate(prophetic)]
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
            && forall<i> 0 <= i && i < visited.len() ==>
                visited[i].deep_model() == self.start.deep_model() + i
        }
    }

    #[law]
    #[ensures(self.produces(Seq::EMPTY, self))]
    fn produces_refl(self) {}

    #[law]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

#[cfg(feature = "nightly")]
impl<Idx: DeepModel<DeepModelTy = Int> + Step> DoubleEndedIterator for Range<Idx> {
    #[predicate]
    #[open]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.start == o.start && self.end.deep_model() >= o.end.deep_model()
            && (visited.len() > 0 ==> o.end.deep_model() >= o.start.deep_model())
            && visited.len() == o.end.deep_model() - self.end.deep_model()
            && forall<i> 0 <= i && i < visited.len() ==>
                visited[i].deep_model() == self.end.deep_model() - i
        }
    }

    #[law]
    #[ensures(self.produces_back(Seq::EMPTY, self))]
    fn produces_back_refl(self) {}

    #[law]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

#[logic]
#[open]
#[ensures(r.is_empty_log() == (result == 0))]
pub fn range_inclusive_len<Idx: DeepModel<DeepModelTy = Int>>(r: RangeInclusive<Idx>) -> Int {
    pearlite! {
        if r.is_empty_log() { 0 }
        else { r.end_log().deep_model() - r.start_log().deep_model() + 1 }
    }
}

#[cfg(feature = "nightly")]
impl<Idx: DeepModel<DeepModelTy = Int> + Step> Iterator for RangeInclusive<Idx> {
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
            forall<i> 0 <= i && i < visited.len() ==>
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

#[cfg(feature = "nightly")]
impl<Idx: DeepModel<DeepModelTy = Int> + Step> DoubleEndedIterator for RangeInclusive<Idx> {
    #[predicate]
    #[open]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            visited.len() == range_inclusive_len(self) - range_inclusive_len(o) &&
            (self.is_empty_log() ==> o.is_empty_log()) &&
            (o.is_empty_log() || self.start_log() == o.start_log()) &&
            forall<i> 0 <= i && i < visited.len() ==>
                visited[i].deep_model() == self.end_log().deep_model() - i
        }
    }

    #[law]
    #[open]
    #[ensures(self.produces_back(Seq::EMPTY, self))]
    fn produces_back_refl(self) {}

    #[law]
    #[open]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

/// Dummy impls that don't use the unstable trait Step
#[cfg(not(feature = "nightly"))]
macro_rules! impl_range {
    ( $( $ty:tt ),+ ) => {
        $(
            impl Iterator for Range<$ty> {}
            impl Iterator for RangeInclusive<$ty> {}
            impl DoubleEndedIterator for Range<$ty> {}
            impl DoubleEndedIterator for RangeInclusive<$ty> {}
        )+
    };
}

#[cfg(not(feature = "nightly"))]
impl_range! { char, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize }
