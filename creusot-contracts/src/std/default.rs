use crate::*;

#[cfg(creusot)]
pub use creusot_contracts_proc::Default;

/// Extension of the standard [`Default`](::std::default::Default) trait.
///
/// This allows Creusot to specify the behavior of [`default`](::std::default::Default::default).
///
/// # Derive macro
///
/// Similarly to `std`, Creusot defines a derive macro for `Default`:
/// ```
/// use creusot_contracts::Default;
///
/// #[derive(Default)]
/// struct S(i32);
/// ```
///
/// This will implement both `Default` traits, and generate a proof obligation to show
/// that they agree.
pub trait Default: ::std::default::Default {
    #[predicate(prophetic)]
    fn is_default(self) -> bool;
}

extern_spec! {
    mod std {
        mod default {
            trait Default where Self : Default {
                #[ensures(result.is_default())]
                fn default() -> Self;
            }
        }
    }
}

impl Default for bool {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { self == false }
    }
}

// `RandomState::default()` is defined as `RandomState::new()`
// which produces random values.
impl Default for std::hash::RandomState {
    #[predicate]
    #[open]
    fn is_default(self) -> bool {
        pearlite! { true }
    }
}
