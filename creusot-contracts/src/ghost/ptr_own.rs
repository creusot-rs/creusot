//! Raw pointers with ghost code

use std::marker::PhantomData;

use crate::prelude::*;
#[cfg(creusot)]
use crate::std::{
    mem::{size_of_logic, size_of_val_logic},
    ptr::{metadata_logic, metadata_matches},
};

/// Token that represents the ownership of a memory cell
///
/// A `PtrOwn` value only exists in the ghost world, but can be used
/// in combination with a corresponding `*const` to access and modify memory.
///
/// A warning regarding memory leaks: dropping a `Ghost<PtrOwn<T>>` (we only
/// ever handle ghost `PtrOwn` values) cannot deallocate the memory
/// corresponding to the pointer because it is a ghost value. One must thus
/// remember to explicitly call [`drop`] in order to free the memory tracked by a
/// `PtrOwn` token.
///
/// # Safety
///
/// When using Creusot to verify the code, all methods should be safe to call. Indeed,
/// Creusot ensures that every operation on the inner value uses the right [`PtrOwn`] object
/// created by [`PtrOwn::new`], ensuring safety in a manner similar to [ghost_cell](https://docs.rs/ghost-cell/latest/ghost_cell/).
///
/// # `#[check(terminates)]`
///
/// `PtrOwn` methods, particularly constructors (`new`, `from_box`, `from_ref`,
/// `from_mut`), are marked `check(terminates)` rather than `check(ghost)`
/// to prevent two things from happening in ghost code:
/// 1. running out of pointer addresses;
/// 2. allocating too large objects.
///
/// Note that we already can't guard against these issues in program code.
/// But preventing them in ghost code is even more imperative to ensure soundness.
///
/// Specifically, creating too many pointers contradicts the [`PtrOwn::disjoint_lemma`],
/// and allocating too large objects contradicts the [`PtrOwn::invariant`] that
/// allocations have size at most `isize::MAX`.
#[allow(dead_code)]
#[opaque]
pub struct PtrOwn<T: ?Sized>(PhantomData<T>);

impl<T: ?Sized> PtrOwn<T> {
    /// The raw pointer whose ownership is tracked by this `PtrOwn`
    #[logic(opaque)]
    pub fn ptr(self) -> *const T {
        dead
    }

    /// The value currently stored at address [`self.ptr()`](Self::ptr)
    #[logic(opaque)]
    pub fn val<'a>(self) -> &'a T {
        dead
    }
}

impl<T: ?Sized> Invariant for PtrOwn<T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            !self.ptr().is_null_logic()
                && self.ptr_is_aligned_opaque()
                && metadata_matches(*self.val(), metadata_logic(self.ptr()))
                // Allocations can never be larger than `isize` (source: https://doc.rust-lang.org/std/ptr/index.html#allocation)
                && size_of_val_logic(*self.val()) <= isize::MAX@
                // The allocation fits in the address space
                // (this is needed to verify (a `PtrOwn` variant of) `<*const T>::add`, which checks this condition)
                && self.ptr().addr_logic()@ + size_of_val_logic(*self.val()) <= usize::MAX@
                && inv(self.val())
        }
    }
}

impl<T> PtrOwn<T> {
    /// Creates a new `PtrOwn` and associated `*const` by allocating a new memory
    /// cell initialized with `v`.
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == v)]
    pub fn new(v: T) -> (*mut T, Ghost<PtrOwn<T>>) {
        Self::from_box(Box::new(v))
    }

    /// If one owns two `PtrOwn`s for non-zero sized types, then they are for different pointers.
    #[trusted]
    #[check(ghost)]
    #[requires(size_of_logic::<T>() != 0)]
    #[ensures(own1.ptr().addr_logic() != own2.ptr().addr_logic())]
    #[ensures(*own1 == ^own1)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(own1: &mut PtrOwn<T>, own2: &PtrOwn<T>) {}
}

impl<T: ?Sized> PtrOwn<T> {
    /// Creates a ghost `PtrOwn` and associated `*const` from an existing [`Box`].
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == *val)]
    #[erasure(Box::into_raw)]
    pub fn from_box(val: Box<T>) -> (*mut T, Ghost<PtrOwn<T>>) {
        (Box::into_raw(val), Ghost::conjure())
    }

    /// Decompose a shared reference into a raw pointer and a ghost `PtrOwn`.
    ///
    /// # Erasure
    ///
    /// This function erases to a raw reborrow of a reference.
    ///
    /// ```ignore
    /// PtrOwn::from_ref(r)
    /// // erases to
    /// r as *const T  // or *mut T (both are allowed)
    /// ```
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0)]
    #[ensures(*result.1.val() == *r)]
    #[intrinsic("ptr_own_from_ref")]
    pub fn from_ref(r: &T) -> (*const T, Ghost<&PtrOwn<T>>) {
        (r, Ghost::conjure())
    }

    /// Decompose a mutable reference into a raw pointer and a ghost `PtrOwn`.
    ///
    /// # Erasure
    ///
    /// This function erases to a raw reborrow of a reference.
    ///
    /// ```ignore
    /// PtrOwn::from_mut(r)
    /// // erases to
    /// r as *const T  // or *mut T (both are allowed)
    /// ```
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0)]
    #[ensures(*result.1.val() == *r)]
    #[ensures(*(^result.1.inner_logic()).val() == ^r)]
    #[intrinsic("ptr_own_from_mut")]
    pub fn from_mut(r: &mut T) -> (*mut T, Ghost<&mut PtrOwn<T>>) {
        (r, Ghost::conjure())
    }

    /// Immutably borrows the underlying `T`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as a direct dereference: `&*ptr`.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PtrOwn).
    ///
    /// # Erasure
    ///
    /// This function erases to a cast from raw pointer to shared reference.
    ///
    /// ```ignore
    /// PtrOwn::as_ref(ptr, own)
    /// // erases to
    /// & *ptr
    /// ```
    #[trusted]
    #[check(terminates)]
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    #[intrinsic("ptr_own_as_ref")]
    pub unsafe fn as_ref(ptr: *const T, own: Ghost<&PtrOwn<T>>) -> &T {
        unsafe { &*ptr }
    }

    /// Mutably borrows the underlying `T`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as a direct dereference: `&mut *ptr`.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PtrOwn).
    ///
    /// # Erasure
    ///
    /// This function erases to a cast from raw pointer to mutable reference.
    ///
    /// ```ignore
    /// PtrOwn::as_mut(ptr, own)
    /// // erases to
    /// &mut *ptr
    /// ```
    #[trusted]
    #[check(terminates)]
    #[allow(unused_variables)]
    #[requires(ptr as *const T == own.ptr())]
    #[ensures(*result == *own.val())]
    #[ensures((^own).ptr() == own.ptr())]
    #[ensures(*(^own).val() == ^result)]
    #[intrinsic("ptr_own_as_mut")]
    pub unsafe fn as_mut(ptr: *mut T, own: Ghost<&mut PtrOwn<T>>) -> &mut T {
        unsafe { &mut *ptr }
    }

    /// Transfers ownership of `own` back into a [`Box`].
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as [`Box::from_raw`].
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PtrOwn).
    #[trusted]
    #[check(terminates)]
    #[requires(ptr as *const T == own.ptr())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    #[erasure(Box::from_raw)]
    pub unsafe fn to_box(ptr: *mut T, own: Ghost<PtrOwn<T>>) -> Box<T> {
        unsafe { Box::from_raw(ptr) }
    }

    /// Deallocates the memory pointed by `ptr`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as [`Box::from_raw`].
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PtrOwn).
    #[check(terminates)]
    #[requires(ptr as *const T == own.ptr())]
    pub unsafe fn drop(ptr: *mut T, own: Ghost<PtrOwn<T>>) {
        let _ = unsafe { Self::to_box(ptr, own) };
    }

    /// The pointer of a `PtrOwn` is always aligned.
    #[check(ghost)]
    #[ensures(self.ptr().is_aligned_logic())]
    pub fn ptr_is_aligned_lemma(&self) {}

    /// Opaque wrapper around [`std::ptr::is_aligned_logic`].
    /// We use this to hide alignment logic by default in `invariant` because it confuses SMT solvers sometimes.
    /// The underlying property is exposed by [`PtrOwn::ptr_is_aligned_lemma`].
    #[logic(open(self))]
    pub fn ptr_is_aligned_opaque(self) -> bool {
        self.ptr().is_aligned_logic()
    }
}
