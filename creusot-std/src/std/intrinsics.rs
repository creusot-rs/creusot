use crate::prelude::*;

extern_spec! {
    mod core {
        mod intrinsics {
            #[check(ghost)]
            fn ub_checks() -> bool;

            #[check(ghost)]
            #[requires(false)]
            unsafe fn unreachable() -> !;

            #[erasure]
            #[check(ghost)]
            #[requires(b)]
            unsafe fn assume(b: bool) {
                if !b {
                    unsafe { core::intrinsics::unreachable() }
                }
            }

            #[check(ghost)]
            #[ensures(result == crate::std::mem::discriminant_value_logic(*v))]
            fn discriminant_value<T>(v: &T) -> <T as std::marker::DiscriminantKind>::Discriminant;
        }
    }
}
