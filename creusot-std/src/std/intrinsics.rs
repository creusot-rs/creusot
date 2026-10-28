use crate::prelude::*;
#[cfg(creusot)]
use crate::std::mem::{align_of_logic, size_of_logic};

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
            #[logic_alias(discriminant_value_logic(*v))]
            fn discriminant_value<T>(v: &T) -> <T as core::marker::DiscriminantKind>::Discriminant;

            // This intrinsic is used by the constant `SizedTypeProperties::SIZE`
            #[check(terminates)]
            #[ensures(result@ == size_of_logic::<T>())]
            #[rustc_comptime]
            fn size_of<T>() -> usize;

            // This intrinsic is used by the constant `SizedTypeProperties::ALIGN`
            #[check(terminates)]
            #[ensures(result == align_of_logic::<T>())]
            #[rustc_comptime]
            fn align_of<T>() -> usize;
        }
    }
}

#[logic(open, inline)]
#[intrinsic("discriminant_value_logic")]
pub fn discriminant_value_logic<T>(_: T) -> <T as core::marker::DiscriminantKind>::Discriminant {
    dead
}
