use crate::prelude::*;
#[cfg(creusot)]
use std::range::{Range, RangeFrom, RangeInclusive, legacy};

extern_spec! {
    impl<T> From<Range<T>> for legacy::Range<T> {
        #[erasure]
        #[ensures(result == legacy::Range { start: value.start, end: value.end })]
        fn from(value: Range<T>) -> Self {
            legacy::Range { start: value.start, end: value.end }
        }
    }

    impl<T> From<legacy::Range<T>> for Range<T> {
        #[erasure]
        #[ensures(result == Range { start: value.start, end: value.end })]
        fn from(value: legacy::Range<T>) -> Self {
            Range { start: value.start, end: value.end }
        }
    }

    impl<T> From<RangeFrom<T>> for legacy::RangeFrom<T> {
        #[erasure]
        #[ensures(result == legacy::RangeFrom { start: value.start })]
        fn from(value: RangeFrom<T>) -> Self {
            legacy::RangeFrom { start: value.start }
        }
    }

    impl<T> From<legacy::RangeFrom<T>> for RangeFrom<T> {
        #[erasure]
        #[ensures(result == RangeFrom { start: value.start })]
        fn from(value: legacy::RangeFrom<T>) -> Self {
            RangeFrom { start: value.start }
        }
    }

    impl<T> From<RangeInclusive<T>> for legacy::RangeInclusive<T> {
        #[erasure]
        #[ensures(result.start_log() == value.start)]
        #[ensures(result.end_log() == value.last)]
        #[ensures(value.start.deep_model() <= value.last.deep_model() ==> !result.is_empty_log())]
        fn from(value: RangeInclusive<T>) -> Self where T: DeepModel<DeepModelTy: OrdLogic> {
            legacy::RangeInclusive::new(value.start, value.last)
        }
    }

    // Note: the other impl `From<legacy::RangeInclusive<T>> for range::RangeInclusive<T>` is partial...
}
