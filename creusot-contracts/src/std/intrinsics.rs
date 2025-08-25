use crate::{ghost::PtrLive, prelude::*};

/// [`<*const T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add) with `PtrOwn` permissions.
///
/// The four functions
///
/// - [`add_live`] (this function)
/// - [`offset_live`]
/// - [`add_live_mut`]
/// - [`offset_live_mut`]
///
/// are wrappers around [`core::intrinsics::offset`]
/// with ghost permission tokens (`PtrOwn`) that allow proving the safety conditions of that intrinsic.
///
/// These four wrappers correspond to the four combinations of `*const T`/`*mut T` and `usize`/`isize`
/// to instantiate [`core::intrinsics::offset`], mirroring the four pointer methods defined in `core`.
///
/// - [`<*const T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add)
/// - [`<*const T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset)
/// - [`<*mut T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add-1)
/// - [`<*mut T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset-1)
///
/// # Safety
///
/// Source: <https://doc.rust-lang.org/core/intrinsics/fn.offset.html>
///
/// > If the computed offset is non-zero, then both the starting and resulting pointer must be either in bounds or at the end of an allocation.
/// > If either pointer is out of bounds or arithmetic overflow occurs then this operation is undefined behavior.
///
/// The preconditions ensure that the `live` witness contains the range between `dst` and `dst + offset`,
/// which prevents out-of-bounds access and overflow.
#[cfg(feature = "nightly")]
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(offset@ == 0 || live.contains(dst))]
#[requires(offset@ == 0 || live.contains(dst.offset_logic(offset@)))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn add_live<T>(dst: *const T, offset: usize, live: Ghost<&PtrLive<T>>) -> *const T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

/// [`<*const T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset) with `PtrOwn` permissions.
///
/// See also [`add_live`]. This function is the variant of `add_live` with `isize` offsets.
#[cfg(feature = "nightly")]
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(offset@ == 0 || live.contains(dst))]
#[requires(offset@ == 0 || live.contains(dst.offset_logic(offset@)))]
#[ensures(result == dst.offset_logic(offset@))]
pub unsafe fn offset_live<T>(dst: *const T, offset: isize, live: Ghost<&PtrLive<T>>) -> *const T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

/// [`<*mut T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add-1) with `PtrOwn` permissions.
///
/// See also [`add_live`]. This function is the variant of `add_live` with `*mut` pointers.
#[cfg(feature = "nightly")]
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(offset@ == 0 || live.contains(dst))]
#[requires(offset@ == 0 || live.contains(dst.offset_logic(offset@)))]
#[ensures(result as *const T == (dst as *const T).offset_logic(offset@))]
pub unsafe fn add_live_mut<T>(dst: *mut T, offset: usize, live: Ghost<&PtrLive<T>>) -> *mut T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

/// [`<*mut T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset-1) with `PtrOwn` permissions.
///
/// See also [`add_live`]. This function is the variant of `add_live` with `*mut` pointers and `isize` offsets.
#[cfg(feature = "nightly")]
#[trusted]
#[erasure(core::intrinsics::offset)]
#[requires(offset@ == 0 || live.contains(dst))]
#[requires(offset@ == 0 || live.contains(dst.offset_logic(offset@)))]
#[ensures(result as *const T == (dst as *const T).offset_logic(offset@))]
pub unsafe fn offset_live_mut<T>(dst: *mut T, offset: isize, live: Ghost<&PtrLive<T>>) -> *mut T {
    unsafe { core::intrinsics::offset(dst, offset) }
}

#[cfg(not(feature = "nightly"))]
pub unsafe fn add_live<T>(dst: *const T, offset: usize, _live: Ghost<&PtrLive<T>>) -> *const T {
    unsafe { dst.add(offset) }
}

#[cfg(not(feature = "nightly"))]
pub unsafe fn offset_live<T>(dst: *const T, offset: isize, _live: Ghost<&PtrLive<T>>) -> *const T {
    unsafe { dst.offset(offset) }
}

#[cfg(not(feature = "nightly"))]
pub unsafe fn add_live_mut<T>(dst: *mut T, offset: usize, _live: Ghost<&PtrLive<T>>) -> *mut T {
    unsafe { dst.add(offset) }
}

#[cfg(not(feature = "nightly"))]
pub unsafe fn offset_live_mut<T>(dst: *mut T, offset: isize, _live: Ghost<&PtrLive<T>>) -> *mut T {
    unsafe { dst.offset(offset) }
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
