use crate::*;
pub use ::std::clone::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::Clone;

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
        #[ensures(result == *self)]
        fn clone(&self) -> bool {
            *self
        }
    }

    impl Clone for f32 {
        #[ensures(result == *self)]
        fn clone(&self) -> f32 {
            *self
        }
    }

    impl Clone for f64 {
        #[ensures(result == *self)]
        fn clone(&self) -> f64 {
            *self
        }
    }

    impl<'a, T: ?Sized> Clone for &'a T {
        #[ensures(result == *self)]
        fn clone(&self) -> &'a T {
            *self
        }
    }
}
