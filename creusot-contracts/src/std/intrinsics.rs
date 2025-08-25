use crate::{ghost::PtrLive, *};

/// `core::intrinsics::offset` intrinsic with `PtrOwn` permissions.
///
/// Safety (<https://doc.rust-lang.org/core/intrinsics/fn.offset.html>):
///
/// > If the computed offset is non-zero, then both the starting and resulting pointer must be either in bounds or at the end of an allocation.
/// > If either pointer is out of bounds or arithmetic overflow occurs then this operation is undefined behavior.
///
/// - We ignore the non-zero condition.
/// - The preconditions ensure that the ownership `own` contains the range between `dst` and `dst + offset`,
///   which also implies that arithmetic overflow does not occur.
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains(dst))]
#[requires(live.contains(dst.offset_logic(offset@)))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn add_own<T>(dst: *const T, offset: usize, live: Ghost<&PtrLive<T>>) -> *const T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

/// Variant of [`add_own`] with `isize` offsets.
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains(dst))]
#[requires(live.contains(dst.offset_logic(offset@)))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn offset_own<T>(dst: *const T, offset: isize, live: Ghost<&PtrLive<T>>) -> *const T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

/// Variant of [`add_own`] with `*mut` pointers.
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains(dst))]
#[requires(live.contains(dst.offset_logic(offset@)))]
#[ensures(result as *const T == (dst as *const T).offset_logic(offset@))]
pub unsafe fn add_own_mut<T>(dst: *mut T, offset: usize, live: Ghost<&PtrLive<T>>) -> *mut T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

/// Variant of [`add_own`] with `*mut` pointers and `isize` offsets.
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(live.contains(dst))]
#[requires(live.contains(dst.offset_logic(offset@)))]
#[ensures(result as *const T == (dst as *const T).offset_logic(offset@))]
pub unsafe fn offset_own_mut<T>(
    dst: *const T,
    offset: isize,
    live: Ghost<&PtrLive<T>>,
) -> *const T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

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

            // `core::intrinsics::arith_offset` has no safety requirements.
            #[ensures(result == dst.offset_logic(offset@))]
            unsafe fn arith_offset<T>(dst: *const T, offset: isize) -> *const T;
        }
    }
}
