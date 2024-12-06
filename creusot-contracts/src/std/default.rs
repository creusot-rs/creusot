use crate::*;
pub use ::std::default::*;

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
