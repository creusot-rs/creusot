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

            // This intrinsic is used by the constant `SizedTypeProperties::SIZE`
            #[check(terminates)]
            #[ensures(result@ == size_of_logic::<T>())]
            fn size_of<T>() -> usize;

            // This intrinsic is used by the constant `SizedTypeProperties::ALIGN`
            #[check(terminates)]
            #[ensures(result == align_of_logic::<T>())]
            fn align_of<T>() -> usize;
        }
    }
}
