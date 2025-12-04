use crate::prelude::*;
use core::clone::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::Clone;

#[cfg(not(creusot))]
pub use core::clone::Clone;

extern_spec! {
    mod std {
        mod clone {
            trait Clone {
                #[requires(true)]
                fn clone(&self) -> Self;
            }
        }
    }

    impl Clone for bool {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> bool {
            *self
        }
    }

    impl Clone for f32 {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> f32 {
            *self
        }
    }

    impl Clone for f64 {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> f64 {
            *self
        }
    }

    impl<'a, T: ?Sized> Clone for &'a T {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> &'a T {
            *self
        }
    }
}
