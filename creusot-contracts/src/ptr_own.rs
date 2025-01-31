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
/// A warning regarding memory leaks: dropping a `GhostBox<PtrOwn<T>>` (we only
/// ever handle ghost `PtrOwn` values) cannot deallocate the memory
/// corresponding to the pointer because it is a ghost value. One must thus
/// remember to explicitly call [`drop`] in order to free the memory tracked by a
/// `PtrOwn` token.
#[trusted]
pub struct PtrOwn<T: ?Sized>(std::marker::PhantomData<T>);

impl<T: ?Sized> PtrOwn<T> {
    /// The raw pointer whose ownership is tracked by this `PtrOwn`
    #[trusted]
    #[logic]
    pub fn ptr(&self) -> RawPtr<T> {
        dead
    }

    /// The value currently stored at address [`self.ptr()`](Self::ptr)
    #[trusted]
    #[logic]
    pub fn val(&self) -> SizedW<T> {
        dead
    }
}

impl<T: ?Sized> Invariant for PtrOwn<T> {
    #[predicate(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { !self.ptr().is_null_logic() && inv(self.val()) }
    }
}

impl<T> PtrOwn<T> {
    /// Creates a new `PtrOwn` and associated [`RawPtr`] by allocating a new memory
    /// cell initialized with `v`.
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == v)]
    pub fn new(v: T) -> (RawPtr<T>, GhostBox<PtrOwn<T>>) {
        Self::from_box(Box::new(v))
    }
}

impl<T: ?Sized> PtrOwn<T> {
    /// Creates a ghost `PtrOwn` and associated [`RawPtr`] from an existing [`Box`].
    #[trusted]
    #[ensures(result.1.ptr() == result.0 && *result.1.val() == *val)]
    pub fn from_box(val: Box<T>) -> (RawPtr<T>, GhostBox<PtrOwn<T>>) {
        assert!(core::mem::size_of_val::<T>(&*val) > 0, "PtrOwn doesn't support ZSTs");
        (Box::into_raw(val), GhostBox::conjure())
    }

    /// Immutably borrows the underlying `T`.
    #[trusted]
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    pub fn as_ref(ptr: RawPtr<T>, own: GhostBox<&PtrOwn<T>>) -> &T {
        unsafe { &*ptr }
    }

    /// Mutably borrows the underlying `T`.
    #[trusted]
    #[allow(unused_variables)]
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    // Currently .inner_logic() is needed instead of *; see issue #1257
    #[ensures((^own.inner_logic()).ptr() == own.ptr())]
    #[ensures(*(^own.inner_logic()).val() == ^result)]
    pub fn as_mut(ptr: RawPtr<T>, own: GhostBox<&mut PtrOwn<T>>) -> &mut T {
        unsafe { &mut *(ptr as *mut _) }
    }

    /// Transfers ownership of `own` back into a [`Box`].
    #[trusted]
    #[requires(ptr == own.ptr())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    pub fn to_box(ptr: RawPtr<T>, own: GhostBox<PtrOwn<T>>) -> Box<T> {
        unsafe { Box::from_raw(ptr as *mut _) }
    }

    /// Deallocates the memory pointed by `ptr`.
    #[requires(ptr == own.ptr())]
    pub fn drop(ptr: RawPtr<T>, own: GhostBox<PtrOwn<T>>) {
        let _ = Self::to_box(ptr, own);
    }

    /// If one owns two `PtrOwn`s in ghost code, then they are for different pointers.
    #[trusted]
    #[pure]
    #[ensures(own1.ptr().addr_logic() != own2.ptr().addr_logic())]
    #[ensures(*own1 == ^own1)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(own1: &mut PtrOwn<T>, own2: &PtrOwn<T>) {
        panic!()
    }
}
