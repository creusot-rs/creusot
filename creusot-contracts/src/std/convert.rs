use crate::prelude::*;
use core::convert::*;

extern_spec! {
    mod core {
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
