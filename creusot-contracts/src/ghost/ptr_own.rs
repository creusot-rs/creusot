//! Raw pointers with ghost code

use ::std::marker::PhantomData;

#[cfg(creusot)]
use crate::std::{
    mem::size_of_logic,
    ptr::{metadata_logic, metadata_matches},
};
use crate::*;

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
        !self.ptr().is_null_logic()
            && self.ptr_is_aligned_opaque()
            && metadata_matches(*self.val(), metadata_logic(self.ptr()))
            && inv(self.ptr())
    }
}

impl<T> PtrOwn<T> {
    /// Creates a new `PtrOwn` and associated `*const` by allocating a new memory
    /// cell initialized with `v`.
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == v)]
    pub fn new(v: T) -> (*const T, Ghost<PtrOwn<T>>) {
        let (x, y) = Self::from_box(Box::new(v));
        (x as *const T, y)
    }

    /// If one owns two `PtrOwn`s in ghost code, with a non-zero sized type, then they are for different pointers.
    #[trusted]
    #[check(ghost)]
    #[ensures(size_of_logic::<T>() != 0 ==> own1.ptr().addr_logic() != own2.ptr().addr_logic())]
    #[ensures(*own1 == ^own1)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(own1: &mut PtrOwn<T>, own2: &PtrOwn<T>) {}

    /// Convert `&PtrOwn<T>` into `&PtrOwn<[T]>` representing a singleton slice.
    #[trusted]
    #[check(ghost_trusted)]
    #[ensures(result.ptr().as_ptr_logic() == self.ptr())]
    #[ensures(result.val()@ == Seq::singleton(*self.val()))]
    pub fn as_slice_own_ref_ghost(&self) -> &PtrOwn<[T]> {
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert `&mut PtrOwn<T>` into `&mut PtrOwn<[T]>` representing a singleton slice.
    #[trusted]
    #[check(ghost_trusted)]
    #[ensures(result.ptr().as_ptr_logic() == self.ptr())]
    #[ensures(result.val()@ == Seq::singleton(*self.val()))]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures((^result).val()@ == Seq::singleton(*(^self).val()))]
    pub fn as_slice_own_mut_ghost(&mut self) -> &mut PtrOwn<[T]> {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl<T: ?Sized> PtrOwn<T> {
    /// Creates a ghost `PtrOwn` and associated `*const` from an existing [`Box`].
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == *val)]
    #[erasure(Box::into_raw)]
    pub fn from_box(val: Box<T>) -> (*mut T, Ghost<PtrOwn<T>>) {
        assert!(core::mem::size_of_val::<T>(&*val) > 0, "PtrOwn doesn't support ZSTs");
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
    #[check(ghost)]
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
    #[check(ghost)]
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
        unsafe { Box::from_raw(ptr as *mut _) }
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
    #[requires(ptr == own.ptr())]
    pub unsafe fn drop(ptr: *const T, own: Ghost<PtrOwn<T>>) {
        let _ = unsafe { Self::to_box(ptr as *mut T, own) };
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

impl<T> PtrOwn<[T]> {
    /// Raw pointer to the slice buffer.
    #[logic(open)]
    pub fn as_ptr(&self) -> *const T {
        pearlite! { self.ptr() as *const T }
    }

    /// The number of elements in the slice.
    #[logic(open)]
    pub fn len(&self) -> Int {
        pearlite! { self.val()@.len() }
    }

    /// Access the logical element at the given index. `None` if out of bounds.
    #[logic(open)]
    pub fn get(&self, index: Int) -> Option<T> {
        pearlite! { self.val()@.get(index) }
    }

    /// Split a `&PtrOwn<[T]>` into two subslices.
    #[trusted]
    #[check(ghost_trusted)]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ptr().as_ptr_logic() == result.0.ptr().as_ptr_logic() && self.ptr().as_ptr_logic().offset_logic(index) == result.1.ptr().as_ptr_logic())]
    #[ensures(index == result.0.len() && self.len() - index == result.1.len())]
    #[ensures(forall<k: Int> 0 <= k && k < index ==> self.val()@[k] == result.0.val()@[k])]
    #[ensures(forall<k: Int> index <= k && k < self.len() ==> self.val()@[k] == result.1.val()@[k - index])]
    pub fn split_at_ghost(&self, index: Int) -> (&Self, &Self) {
        let _ = index;
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Split a `&mut PtrOwn<[T]>` into two subslices.
    #[trusted]
    #[check(ghost_trusted)]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ptr().as_ptr_logic() == result.0.ptr().as_ptr_logic()  && self.ptr().as_ptr_logic().offset_logic(index) == result.1.ptr().as_ptr_logic())]
    #[ensures(index == result.0.len() && self.len() - index == result.1.len())]
    #[ensures(index == (^result.0).len() && self.len() - index == (^result.1).len())]
    #[ensures(forall<k: Int> 0 <= k && k < index ==> self.val()@[k] == result.0.val()@[k] && (^self).val()@[k] == (^result.0).val()@[k])]
    #[ensures(forall<k: Int> index <= k && k < self.len() ==> self.val()@[k] == result.1.val()@[k - index] && (^self).val()@[k] == (^result.1).val()@[k - index])]
    #[ensures((^self).ptr() == self.ptr())]
    pub fn split_at_mut_ghost(&mut self, index: Int) -> (&mut Self, &mut Self) {
        let _ = index;
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert a `&PtrOwn<[T]>` for a non-empty slice into a `&PtrOwn<T>` for the first element.
    #[trusted]
    #[check(ghost_trusted)]
    #[requires(self.len() > 0)]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic())]
    #[ensures(*result.val() == self.val()@[0])]
    pub fn as_ptr_own_ref_ghost(&self) -> &PtrOwn<T> {
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert a `&mut PtrOwn<[T]>` for a non-empty slice into a `&mut PtrOwn<T>` for the first element.
    #[trusted]
    #[check(ghost_trusted)]
    #[requires(self.len() > 0)]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic())]
    #[ensures(*result.val() == self.val()@[0])]
    #[ensures(*(^result).val() == (^self).val()@[0])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures(forall<i: Int> 0 < i && i < self.len() ==> (^self).val()@[i] == self.val()@[i])]
    pub fn as_ptr_own_mut_ghost(&mut self) -> &mut PtrOwn<T> {
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert a `&PtrOwn<[T]>` for a non-empty slice into a `&PtrOwn<T>` for the element at the given index.
    #[check(ghost)]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    pub fn index_ptr_own_ref_ghost(&self, index: Int) -> &PtrOwn<T> {
        self.split_at_ghost(index).1.as_ptr_own_ref_ghost()
    }

    /// Convert a `&mut PtrOwn<[T]>` for a non-empty slice into a `&mut PtrOwn<T>` for the element at the given index.
    #[check(ghost)]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    #[ensures(*(^result).val() == (^self).val()@[index])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures(forall<k: Int> k != index ==> (^self).val()@.get(k) == self.val()@.get(k))]
    pub fn index_ptr_own_mut_ghost(&mut self, index: Int) -> &mut PtrOwn<T> {
        self.split_at_mut_ghost(index).1.as_ptr_own_mut_ghost()
    }
}
