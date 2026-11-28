use crate::prelude::*;

/// Derives `Clone`.
///
/// This works just like the `std` derive macro except it adds specification to the derived trait
/// and accepts `#[use_DeepModel]` attribute to additionally attach specification that says the
/// deep model of the result is equal to the deep model of `self`. However, this attribute is
/// currently only available for non-generic types because supporting generics properly is much
/// more challenging.
///
/// Because it is not possible to register the attribute for external proc macros the attribute
/// will not get ignored when compiling without creusot. To ensure normal compilation works use
/// `#[cfg_attr(creusot, use_DeepModel)]` instead of plain `#[use_DeepModel]`.
///
/// Important: only fields with visibility at least that of the struct will have their
/// postcondition exposed. This may make code that calls `clone` unprovable. Using `DeepModel` is
/// the recommended solution for most cases in which it is possible.
#[cfg(creusot)]
pub use creusot_std_proc::Clone;

#[cfg(not(creusot))]
pub use core::clone::Clone;

extern_spec! {
    mod core {
        mod clone {
            trait Clone {
                fn clone(&self) -> Self;

                #[ensures(resolve(*self))]
                #[ensures(Self::clone.postcondition((source,), ^self))]
                fn clone_from(&mut self, source: &Self) {
                    *self = source.clone()
                }
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
