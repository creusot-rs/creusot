use crate::prelude::*;
use core::default::*;

#[cfg(creusot)]
pub use creusot_std_proc::Default;

#[cfg(not(creusot))]
pub use core::default::Default;

extern_spec! {
    mod core {
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
