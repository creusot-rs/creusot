//! Raw pointers with ghost code

#[cfg(creusot)]
use crate::util::SizedW;
use crate::*;

/// Raw pointer whose ownership is tracked by a ghost [`PtrOwn`].
pub type RawPtr<T> = *const T;

/// Token that represents the ownership of a memory cell. A `PtrOwn` value only
/// exists in the ghost world, but can be used in combination with a
/// corresponding [`RawPtr`] to access and modify memory.
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
pub struct PtrOwn<T: ?Sized> {
    ptr: RawPtr<T>,
    val: Box<T>,
}

impl<T: ?Sized> PtrOwn<T> {
    /// The raw pointer whose ownership is tracked by this `PtrOwn`
    #[logic]
    pub fn ptr(&self) -> RawPtr<T> {
        self.ptr
    }

    /// The value currently stored at address [`self.ptr()`](Self::ptr)
    #[logic]
    pub fn val(&self) -> SizedW<T> {
        self.val
    }
}

impl<T: ?Sized> Invariant for PtrOwn<T> {
    #[predicate]
    #[open]
    fn invariant(self) -> bool {
        !self.ptr().is_null_logic()
    }
}

impl<T> PtrOwn<T> {
    /// Creates a new `PtrOwn` and associated [`RawPtr`] by allocating a new memory
    /// cell initialized with `v`.
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == v)]
    pub fn new(v: T) -> (RawPtr<T>, Ghost<PtrOwn<T>>) {
        Self::from_box(Box::new(v))
    }

    /// If one owns two `PtrOwn`s in ghost code, with a non-zero sized type, then they are for different pointers.
    #[trusted]
    #[pure]
    #[ensures(size_of_logic::<T>() != 0 ==> own1.ptr() != own2.ptr())]
    #[ensures(*own1 == ^own1)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(own1: &mut PtrOwn<T>, own2: &PtrOwn<T>) {}

    /// Convert `&PtrOwn<T>` into `&PtrOwn<[T]><T>` representing a singleton slice.
    #[trusted]
    #[pure]
    #[ensures(result.ptr().as_ptr_logic() == self.ptr())]
    #[ensures(result.val()@ == Seq::singleton(*self.val()))]
    pub fn as_slice_own_ref_ghost(&self) -> &PtrOwn<[T]> {
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert `&mut PtrOwn<T>` into `&mut PtrOwn<[T]><T>` representing a singleton slice.
    #[trusted]
    #[pure]
    #[ensures(result.ptr().as_ptr_logic() == self.ptr())]
    #[ensures(result.val()@ == Seq::singleton(*self.val()))]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures((^result).val()@ == Seq::singleton(*(^self).val()))]
    pub fn as_slice_own_mut_ghost(&mut self) -> &mut PtrOwn<[T]> {
        unreachable!("BUG: called ghost function in normal code")
    }
}

impl<T: ?Sized> PtrOwn<T> {
    /// Creates a ghost `PtrOwn` and associated [`RawPtr`] from an existing [`Box`].
    #[trusted]
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == *val)]
    pub fn from_box(val: Box<T>) -> (RawPtr<T>, Ghost<PtrOwn<T>>) {
        assert!(core::mem::size_of_val::<T>(&*val) > 0, "PtrOwn doesn't support ZSTs");
        (Box::into_raw(val), Ghost::conjure())
    }

    /// Immutably borrows the underlying `T`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as a direct dereference: `&*ptr`.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PtrOwn).
    #[trusted]
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    pub unsafe fn as_ref(ptr: RawPtr<T>, own: Ghost<&PtrOwn<T>>) -> &T {
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
    #[trusted]
    #[allow(unused_variables)]
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    // Currently .inner_logic() is needed instead of *; see issue #1257
    #[ensures((^own.inner_logic()).ptr() == own.ptr())]
    #[ensures(*(^own.inner_logic()).val() == ^result)]
    pub unsafe fn as_mut(ptr: RawPtr<T>, own: Ghost<&mut PtrOwn<T>>) -> &mut T {
        unsafe { &mut *(ptr as *mut _) }
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
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    pub unsafe fn to_box(ptr: RawPtr<T>, own: Ghost<PtrOwn<T>>) -> Box<T> {
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
    #[requires(ptr == own.ptr())]
    pub unsafe fn drop(ptr: RawPtr<T>, own: Ghost<PtrOwn<T>>) {
        let _ = Self::to_box(ptr, own);
    }
}

impl<T> PtrOwn<[T]> {
    /// Raw pointer to the slice buffer.
    #[logic]
    #[open]
    pub fn as_ptr(&self) -> RawPtr<T> {
        pearlite! { self.ptr() as RawPtr<T> }
    }

    /// The number of elements in the slice.
    /// Invariant: `self.val()@.len() == self.ptr().len_logic()` TODO how to add this to Invariant?
    #[logic]
    #[open]
    pub fn len(&self) -> Int {
        pearlite! { self.val()@.len() }
    }

    /// Access the logical element at the given index. `None` if out of bounds.
    #[logic]
    #[open(self)]
    pub fn get(&self, index: Int) -> Option<T> {
        pearlite! { self.val()@.get(index) }
    }

    /// Split a `&PtrOwn<[T]>` into two subslices.
    #[trusted]
    #[pure]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ptr().as_ptr_logic() == result.0.ptr().as_ptr_logic() && self.ptr().as_ptr_logic().offset_logic(index) == result.1.ptr().as_ptr_logic())]
    #[ensures(result.0.ptr().len_logic() == result.0.len() && result.1.ptr().len_logic() == result.1.len())]
    #[ensures(index == result.0.len() && self.len() - index == result.1.len())]
    #[ensures(forall<k: Int> 0 <= k && k < index ==> self.val()@[k] == result.0.val()@[k])]
    #[ensures(forall<k: Int> index <= k && k < self.len() ==> self.val()@[k] == result.1.val()@[k - index])]
    pub fn split_at_ghost(&self, index: Int) -> (&Self, &Self) {
        let _ = index;
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Split a `&mut PtrOwn<[T]>` into two subslices.
    #[trusted]
    #[pure]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ptr().as_ptr_logic() == result.0.ptr().as_ptr_logic()  && self.ptr().as_ptr_logic().offset_logic(index) == result.1.ptr().as_ptr_logic())]
    #[ensures(result.0.ptr().len_logic() == result.0.len() && result.1.ptr().len_logic() == result.1.len())]
    #[ensures(index == result.0.len() && self.len() - index == result.1.len())]
    #[ensures(index == (^result.0).len() && self.len() - index == (^result.1).len())]
    #[ensures(forall<k: Int> 0 <= k && k < index ==> self.val()@[k] == result.0.val()@[k] && (^self).val()@[k] == (^result.0).val()@[k])]
    #[ensures(forall<k: Int> index <= k && k < self.len() ==> self.val()@[k] == result.1.val()@[k - index] && (^self).val()@[k] == (^result.1).val()@[k - index])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures((^self).len() == self.len())]
    pub fn split_at_mut_ghost(&mut self, index: Int) -> (&mut Self, &mut Self) {
        let _ = index;
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert a `&PtrOwn<[T]>` for a non-empty slice into a `&PtrOwn<T>` for the first element.
    #[trusted]
    #[pure]
    #[requires(self.len() > 0)]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic())]
    #[ensures(*result.val() == self.val()@[0])]
    pub fn as_ptr_own_ref_ghost(&self) -> &PtrOwn<T> {
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert a `&mut PtrOwn<[T]>` for a non-empty slice into a `&mut PtrOwn<T>` for the first element.
    #[trusted]
    #[pure]
    #[requires(self.len() > 0)]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic())]
    #[ensures(*result.val() == self.val()@[0])]
    #[ensures(*(^result).val() == (^self).val()@[0])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures((^self).len() == self.len())]
    #[ensures(forall<i: Int> 0 < i && i < self.len() ==> (^self).val()@[i] == self.val()@[i])]
    pub fn as_ptr_own_mut_ghost(&mut self) -> &mut PtrOwn<T> {
        unreachable!("BUG: called ghost function in normal code")
    }

    /// Convert a `&PtrOwn<[T]>` for a non-empty slice into a `&PtrOwn<T>` for the element at the given index.
    #[pure]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    pub fn index_ptr_own_ref_ghost(&self, index: Int) -> &PtrOwn<T> {
        self.split_at_ghost(index).1.as_ptr_own_ref_ghost()
    }

    /// Convert a `&mut PtrOwn<[T]>` for a non-empty slice into a `&mut PtrOwn<T>` for the element at the given index.
    #[pure]
    #[requires(0 <= index && index < self.len())]
    #[ensures(result.ptr() == self.ptr().as_ptr_logic().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    #[ensures(*(^result).val() == (^self).val()@[index])]
    #[ensures((^self).ptr() == self.ptr())]
    #[ensures((^self).len() == self.len())]
    #[ensures(forall<k: Int> k != index ==> (^self).val()@.get(k) == self.val()@.get(k))]
    pub fn index_ptr_own_mut_ghost(&mut self, index: Int) -> &mut PtrOwn<T> {
        self.split_at_mut_ghost(index).1.as_ptr_own_mut_ghost()
    }
}
