use crate::{
    prelude::*,
    std::iter::{ExactSizeIteratorSpec, StepSpec},
};
use core::ops::{Range, RangeInclusive};

#[cfg(feature = "nightly")]
impl<Idx: StepSpec> IteratorSpec for Range<Idx> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            resolve(self) && self.start.deep_model() >= self.end.deep_model()
        }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.end == o.end && self.start.deep_model() <= o.start.deep_model()
            && (visited.len() > 0 ==> o.start.deep_model() <= o.end.deep_model())
            && self.start.steps(visited.len(), o.start)
            && forall<i> 0 <= i && i < visited.len() ==> self.start.steps(i, visited[i])
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

extern_spec! {
    impl<Idx: StepSpec> Iterator for Range<Idx> {
        #[ensures(self.start.deep_model() >= self.end.deep_model() ==>
            result == (0usize, Some(0usize)))]
        #[ensures(forall<count: Int>
            self.start.steps(count, self.end)
            ==> result == if count <= usize::MAX@ {
                (count.into(), Some(count.into()))
            } else {
                (usize::MAX, None)
            }
        )]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

macro_rules! impl_exact_size_range {
    ($($t:ty)*) => ($(
        impl ExactSizeIteratorSpec for Range<$t> {
            #[logic(law)]
            #[requires(Self::size_hint.postcondition((self,), r))]
            #[ensures(r.1 == Some(r.0))]
            #[allow(unused_variables)]
            fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
        }
    )*)
}

impl_exact_size_range! { i8 u8 i16 u16 isize usize }

// Apparently, `ExactSizeIterator` is not implemented for `Range<i64>` and `Range<u64>` even
// on 64-bit platforms.
#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl_exact_size_range! { i32 u32 }

#[cfg(feature = "nightly")]
impl<Idx: StepSpec> DoubleEndedIteratorSpec for Range<Idx> {
    #[logic(open)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            self.start == o.start && self.end.deep_model() >= o.end.deep_model()
            && (visited.len() > 0 ==> o.end.deep_model() >= o.start.deep_model())
            && self.end.steps(-visited.len(), o.end)
            && forall<i> 0 <= i && i < visited.len() ==> self.end.steps(-i-1, visited[i])
        }
    }

    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.completed()
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}
}

#[cfg(feature = "nightly")]
impl<Idx: StepSpec> IteratorSpec for RangeInclusive<Idx> {
    #[logic(open, prophetic)]
    fn completed(&mut self) -> bool {
        pearlite! {
            self.is_empty_log() && (^self).is_empty_log()
        }
    }

    #[logic(open)]
    fn produces(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            (if self.is_empty_log() {
                visited.len() == 0 && o.is_empty_log()
            } else {
                if o.is_empty_log() {
                    visited.len() > 0 &&
                    self.start_log().steps(
                        visited.len() - 1,
                        self.end_log())
                } else {
                    self.start_log().steps(
                        visited.len(),
                        o.start_log()) &&
                    self.end_log() == o.end_log()
                }
            }) &&
            forall<i> 0 <= i && i < visited.len() ==> self.start_log().steps(i, visited[i])
        }
    }

    #[logic(law)]
    #[ensures(self.produces(Seq::empty(), self))]
    fn produces_refl(self) {}

    #[logic(law)]
    #[requires(a.produces(ab, b))]
    #[requires(b.produces(bc, c))]
    #[ensures(a.produces(ab.concat(bc), c))]
    fn produces_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}
}

extern_spec! {
    impl<Idx: StepSpec> Iterator for RangeInclusive<Idx> {
        #[ensures(self.is_empty_log() ==> result == (0usize, Some(0usize)))]
        #[ensures(forall<count: Int>
            !self.is_empty_log()
            && self.start_log().steps(count, self.end_log())
            ==> result == if count < usize::MAX@ {
                    ((count + 1).into(), Some((count + 1).into()))
                } else {
                    (usize::MAX, None)
                }
        )]
        fn size_hint(&self) -> (usize, Option<usize>);
    }
}

macro_rules! impl_exact_size_range_inclusive {
    ($($t:ty)*) => ($(
        impl ExactSizeIteratorSpec for RangeInclusive<$t> {
            #[logic(law)]
            #[requires(Self::size_hint.postcondition((self,), r))]
            #[ensures(r.1 == Some(r.0))]
            #[allow(unused_variables)]
            fn size_hint_exact(&self, r: (usize, Option<usize>)) {}
        }
    )*)
}

impl_exact_size_range_inclusive! { i8 u8 }

#[cfg(any(target_pointer_width = "32", target_pointer_width = "64"))]
impl_exact_size_range_inclusive! { i16 u16 }

#[cfg(feature = "nightly")]
impl<Idx: StepSpec> DoubleEndedIteratorSpec for RangeInclusive<Idx> {
    #[logic(open)]
    fn produces_back(self, visited: Seq<Self::Item>, o: Self) -> bool {
        pearlite! {
            (if self.is_empty_log() {
                visited.len() == 0 && o.is_empty_log()
            } else {
                if o.is_empty_log() {
                    visited.len() > 0 &&
                    self.end_log().steps(
                        -visited.len() + 1,
                        self.start_log())
                } else {
                    self.end_log().steps(
                        -visited.len(),
                        o.end_log()) &&
                    self.start_log() == o.start_log()
                }
            }) &&
            forall<i> 0 <= i && i < visited.len() ==> self.end_log().steps(-i, visited[i])
        }
    }

    #[logic(open, prophetic)]
    fn completed_back(&mut self) -> bool {
        self.completed()
    }

    #[logic(law)]
    #[ensures(self.produces_back(Seq::empty(), self))]
    fn produces_back_refl(self) {}

    #[logic(law)]
    #[requires(a.produces_back(ab, b))]
    #[requires(b.produces_back(bc, c))]
    #[ensures(a.produces_back(ab.concat(bc), c))]
    fn produces_back_trans(a: Self, ab: Seq<Self::Item>, b: Self, bc: Seq<Self::Item>, c: Self) {}

    #[logic(law)]
    #[requires(Self::size_hint.postcondition((self,), r))]
    #[ensures(forall<s: Seq<Self::Item>, i: &mut Self>
        self.produces_back(s, *i) && i.completed_back() ==> r.0@ <= s.len())]
    #[ensures(match r.1 {
        Some(r) => {
            forall<s: Seq<Self::Item>, i: Self> self.produces_back(s, i) ==> s.len() <= r@
        }
        None => true
    })]
    fn size_hint_back_spec(&self, r: (usize, Option<usize>)) {}
}

/// Dummy impls that don't use the unstable trait Step
#[cfg(not(feature = "nightly"))]
macro_rules! impl_range {
    ( $( $ty:tt ),+ ) => {
        $(
            impl IteratorSpec for Range<$ty> {}
            impl IteratorSpec for RangeInclusive<$ty> {}
            impl DoubleEndedIteratorSpec for Range<$ty> {}
            impl DoubleEndedIteratorSpec for RangeInclusive<$ty> {}
        )+
    };
}

#[cfg(not(feature = "nightly"))]
impl_range! { char, i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize }
