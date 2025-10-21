use crate::prelude::*;
use std::default::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::Default;

#[cfg(not(creusot))]
pub use std::default::Default;

extern_spec! {
    mod std {
        mod default {
            trait Default {
                // #[requires(true)]
                fn default() -> Self;
            }
        }
    }

    impl Default for bool {
        #[check(ghost)]
        #[ensures(result == false)]
        fn default() -> bool;
    }
}
