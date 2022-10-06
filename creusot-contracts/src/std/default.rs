use crate as creusot_contracts;

use creusot_contracts_proc::*;

pub trait Default: std::default::Default {
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

// TODO: use a macro for these instances.
// Problem: the pearlite parer does not support "invisible groups" that will
// appear because of this macro.

impl Default for () {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == () }
    }
}

impl Default for bool {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == false }
    }
}

impl Default for usize {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0usize }
    }
}

impl Default for u8 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0u8 }
    }
}

impl Default for u16 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0u16 }
    }
}

impl Default for u32 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0u32 }
    }
}

impl Default for u64 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0u64 }
    }
}

impl Default for u128 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0u128 }
    }
}

impl Default for isize {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0isize }
    }
}

impl Default for i8 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0i8 }
    }
}

impl Default for i16 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0i16 }
    }
}

impl Default for i32 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0i32 }
    }
}

impl Default for i64 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0i64 }
    }
}

impl Default for i128 {
    #[predicate]
    fn is_default(self) -> bool {
        pearlite! { self == 0i128 }
    }
}
