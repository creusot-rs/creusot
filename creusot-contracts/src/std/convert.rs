use crate::*;

/// Specification trait for `::std::convert::From`.
pub trait From<T>: ::std::convert::From<T> {
    /// Relation between input and output of `from`.
    #[predicate]
    fn comes_from(self, value: T) -> bool;
}

extern_spec! {
    mod std {
        mod convert {
            trait From<T> where Self: From<T> {
                #[ensures(result.comes_from(value))]
                fn from(value: T) -> Self;
            }
        }
    }
}

impl<T> From<T> for T {
    #[predicate]
    #[open]
    fn comes_from(self, value: T) -> bool {
        self == value
    }
}
