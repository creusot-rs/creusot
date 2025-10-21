use crate::prelude::*;
use std::convert::*;

extern_spec! {
    mod std {
        mod convert {
            trait From<T> where Self: From<T> {
                // #[requires(true)]
                fn from(value: T) -> Self;
            }
        }
    }

    impl<T> From<T> for T {
        #[ensures(result == self)]
        fn from(self) -> T;
    }
}
