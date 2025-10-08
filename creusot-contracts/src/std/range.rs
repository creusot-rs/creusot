use crate::*;
#[cfg(creusot)]
use ::std::range::{Range, legacy};

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
}
