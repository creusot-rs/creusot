use crate::*;
pub use ::std::default::*;

pub trait Default: ::std::default::Default {
    #[predicate]
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
    fn is_default(self) -> bool {
        pearlite! { self == false }
    }
}
