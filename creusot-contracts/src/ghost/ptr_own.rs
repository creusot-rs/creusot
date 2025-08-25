//! Raw pointers with ghost code

use std::marker::PhantomData;

use crate::prelude::*;
#[cfg(creusot)]
use crate::std::{
    mem::size_of_logic,
    ptr::{metadata_logic, metadata_matches},
};

/// Token that represents the ownership of a memory cell
///
/// A `PtrOwn` value only exists in the ghost world, but can be used
/// in combination with a corresponding `*const` to access and modify memory.
///
/// `PtrOwn<T>` is unsized so that it cannot be moved out of a `&mut PtrOwn<T>`.
/// This is crucial to ensure the soundness of [`PtrOwn::from_mut`], [`PtrOwn::split_at`],
/// and [`PtrOwn::elements_mut`].
/// We use `Box<PtrOwn<T>>` to represent owned tokens.
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
pub struct PtrOwn<T: ?Sized>([PhantomData<T>]);

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
                && metadata_matches(*self.val(), metadata_logic(self.ptr()))
                && inv(self.val())
        }
    }
}

impl<T> PtrOwn<T> {
    /// Creates a new `PtrOwn` and associated `*const` by allocating a new memory
    /// cell initialized with `v`.
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == v)]
    pub fn new(v: T) -> (*mut T, Ghost<Box<PtrOwn<T>>>) {
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
    pub fn from_box(val: Box<T>) -> (*mut T, Ghost<Box<PtrOwn<T>>>) {
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
    /// r as *mut T
    /// ```
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0)]
    #[ensures(*result.1.val() == *r)]
    #[ensures(*(^*result.1).val() == ^r)]
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
    pub unsafe fn to_box(ptr: *mut T, own: Ghost<Box<PtrOwn<T>>>) -> Box<T> {
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
    pub unsafe fn drop(ptr: *mut T, own: Ghost<Box<PtrOwn<T>>>) {
        let _ = unsafe { Self::to_box(ptr, own) };
    }
}

/// # Permissions for slice pointers
///
/// Core methods:
///
/// - To split a `&PtrOwn<[T]>`: [`split_at`](PtrOwn::split_at), [`split_at_mut`](PtrOwn::split_at_mut).
/// - To index a `&PtrOwn<[T]>` into `&PtrOwn<T>`: [`elements`](PtrOwn::elements), [`elements_mut`](PtrOwn::elements_mut).
/// - To extract a [`&PtrLive<T>`][PtrLive] (evidence used by pointer arithmetic): [`live`](PtrOwn::live), [`live_mut`](PtrOwn::live_mut).
impl<T> PtrOwn<[T]> {
    /// The number of elements in the slice.
    #[logic(open, inline)]
    pub fn len(self) -> Int {
        pearlite! { self.val()@.len() }
    }

    /// Split a `&PtrOwn<[T]>` into two subslices of lengths `index` and `self.len() - index`.
    #[trusted]
    #[check(ghost)]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ptr().thin() == result.0.ptr().thin())]
    #[ensures(self.ptr().thin().offset_logic(index) == result.1.ptr().thin())]
    #[ensures(self.val()@.subsequence(0, index) == result.0.val()@)]
    #[ensures(self.val()@.subsequence(index, self.len()) == result.1.val()@)]
    pub fn split_at(&self, index: Int) -> (&Self, &Self) {
        let _ = index;
        panic!("called ghost function in normal code")
    }

    /// Split a `&mut PtrOwn<[T]>` into two subslices of lengths `index` and `self.len() - index`.
    #[trusted]
    #[check(ghost)]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ptr().thin() == result.0.ptr().thin())]
    #[ensures(self.ptr().thin().offset_logic(index) == result.1.ptr().thin())]
    #[ensures(self.val()@.subsequence(0, index) == result.0.val()@)]
    #[ensures(self.val()@.subsequence(index, self.len()) == result.1.val()@)]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures((^self).val()@.subsequence(0, index) == (^result.0).val()@)]
    #[ensures((^self).val()@.subsequence(index, self.len()) == (^result.1).val()@)]
    pub fn split_at_mut(&mut self, index: Int) -> (&mut PtrOwn<[T]>, &mut PtrOwn<[T]>) {
        let _ = index;
        panic!("called ghost function in normal code")
    }

    /// Split `&PtrOwn<[T]>` into a sequence of `&PtrOwn<T>` for each element.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<i> 0 <= i && i < self.len()
        ==> result[i].ptr() == self.ptr().thin().offset_logic(i)
        && *result[i].val() == self.val()@[i])]
    pub fn elements(&self) -> Seq<&PtrOwn<T>> {
        panic!("called ghost function in normal code")
    }

    /// Split `&mut PtrOwn<[T]>` into a sequence of `&mut PtrOwn<T>` for each element.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<i> 0 <= i && i < self.len()
        ==> result[i].ptr() == self.ptr().thin().offset_logic(i)
        && *result[i].val() == self.val()@[i])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures(forall<i> 0 <= i && i < self.len() ==> *(^result[i]).val() == (^self).val()@[i])]
    pub fn elements_mut(&mut self) -> Seq<&mut PtrOwn<T>> {
        panic!("called ghost function in normal code")
    }

    /// Index a `&PtrOwn<[T]>` into a `&PtrOwn<T>`.
    #[check(ghost)]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result.ptr() == self.ptr().thin().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    pub fn index(&self, index: Int) -> &PtrOwn<T> {
        let mut r = self.elements();
        r.split_off_ghost(index).pop_front_ghost().unwrap()
    }

    /// Index a `&mut PtrOwn<[T]>` into a `&mut PtrOwn<T>`.
    #[check(ghost)]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result.ptr() == self.ptr().thin().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures(*(^result).val() == (^self).val()@[index])]
    // TODO: The next ensures is only to help solvers figure out the last one. We should find another workaround.
    #[ensures(forall<k: Int> index < k ==> (^self).val()@.get(k) == self.val()@.get(k))]
    // TODO: Alt-Ergo takes 3s to prove this. Some trigger nonsense is going on.
    #[ensures(forall<k: Int> k != index ==> (^self).val()@.get(k) == self.val()@.get(k))]
    pub fn index_mut(&mut self, index: Int) -> &mut PtrOwn<T> {
        let mut r = self.elements_mut();
        proof_assert! { forall<k> index < k && k < r.len() ==> r[k].val() == r.subsequence(index, r.len()).tail()[k-index-1].val() };
        r.split_off_ghost(index).pop_front_ghost().unwrap()
    }

    /// Extract `PtrLive<'a, T>` from `&PtrOwn<'a, [T]>`.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.ptr() == self.ptr().thin())]
    #[ensures(result.len()@ == self.len())]
    pub fn live(&self) -> PtrLive<'_, T> {
        panic!("called ghost function in normal code")
    }

    /// Extract `PtrLive<'a, T>` from `&mut PtrOwn<[T]>`.
    ///
    /// The borrow is returned so that it can be used at the same time as the `PtrLive` token.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.0 == self)]
    #[ensures(result.1.ptr() == self.ptr().thin())]
    #[ensures(result.1.len()@ == self.len())]
    pub fn live_mut(&mut self) -> (&mut Self, PtrLive<'_, T>) {
        panic!("called ghost function in normal code")
    }
}

/// Evidence that a range of memory is alive.
///
/// This evidence enables taking pointer offsets (see [`add_live`](crate::std::intrinsics::add_live) and others)
/// without ownership (via [`PtrOwn`]) of that range of memory.
///
/// Its lifetime is bounded by some `&PtrOwn<[T]>` (via `PtrOwn::live` or `PtrOwn::live_mut`).
#[opaque]
pub struct PtrLive<'a, T>(PhantomData<&'a T>);

impl<T> Clone for PtrLive<'_, T> {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        panic!("called ghost function in normal code")
    }
}

impl<T> Copy for PtrLive<'_, T> {}

/// This invariant makes explicit certain facts about the layout of allocations
/// which are otherwise invisible in `PtrOwn`. If you have a `&PtrOwn`, you can make
/// these facts known by calling [`PtrOwn::live`].
impl<T> Invariant for PtrLive<'_, T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            // Allocations can never be larger than `isize` bytes
            // (source: <https://doc.rust-lang.org/std/ptr/index.html#allocation>)
            self.len()@ * size_of_logic::<T>() <= isize::MAX@
            // The allocation fits in the address space
            // (this is needed to verify (a `PtrOwn` variant of) `<*const T>::add`, which checks this condition)
            && self.ptr().addr_logic()@ + self.len()@ * size_of_logic::<T>() <= usize::MAX@
            // The pointer of a `PtrOwn` is always aligned.
            && self.ptr().is_aligned_logic()
        }
    }
}

impl<T> PtrLive<'_, T> {
    /// Base pointer, start of the range
    #[trusted]
    #[logic(opaque)]
    pub fn ptr(self) -> *const T {
        dead
    }

    /// The number of elements (of type `T`) in the range.
    ///
    /// The length in bytes is thus `self.len()@ * size_of_logic::<T>()`.
    #[trusted]
    #[logic(opaque)]
    pub fn len(self) -> usize {
        dead
    }

    /// The live range contains `ptr`
    #[logic(open, inline)]
    pub fn contains(self, ptr: *const T) -> bool {
        pearlite! {
            let offset = ptr.sub_logic(self.ptr());
            ptr == self.ptr().offset_logic(offset)
            && 0 <= offset && offset <= self.len()@
        }
    }
}
