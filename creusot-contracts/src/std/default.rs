use crate::*;
pub use ::std::default::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::Default;

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
        #[ensures(result == false)]
        fn default() -> bool;
    }
}
