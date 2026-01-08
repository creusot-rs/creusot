//! Shared mutation with a ghost token
//!
//! This allows a form of interior mutability, using [ghost](mod@crate::ghost) code to keep
//! track of the logical value.

use crate::{
    ghost::perm::{Container, Perm},
    prelude::*,
};
use core::cell::UnsafeCell;

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

/// Cell with ghost permissions
///
/// When writing/reading the cell, you need to explicitly pass a [`Perm`] object.
///
/// # Safety
///
/// When using Creusot to verify the code, all methods should be safe to call. Indeed,
/// Creusot ensures that every operation on the inner value uses the right [`Perm`] object
/// created by [`PermCell::new`], ensuring safety in a manner similar to
/// [ghost_cell](https://docs.rs/ghost-cell/latest/ghost_cell/).
#[repr(transparent)]
#[opaque]
pub struct PermCell<T: ?Sized>(UnsafeCell<T>);

impl<T: Sized> Container for PermCell<T> {
    type Value = T;

    #[logic(open, inline)]
    fn is_disjoint(&self, _: &T, other: &Self, _: &T) -> bool {
        self != other
    }
}

impl<T: Sized> Invariant for Perm<PermCell<T>> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { inv(self.val()) }
    }
}

impl<T> PermCell<T> {
    /// Creates a new `PermCell` containing the given value.
    #[trusted]
    #[check(terminates)]
    #[ensures(result.0 == *result.1.ward())]
    #[ensures((*result.1)@ == value)]
    pub fn new(value: T) -> (Self, Ghost<Box<Perm<PermCell<T>>>>) {
        let this = Self(UnsafeCell::new(value));
        let perm = Ghost::conjure();
        (this, perm)
    }

    /// Sets the contained value.
    ///
    /// # Safety
    ///
    /// You must ensure that no other borrows to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PermCell#safety).
    #[trusted]
    #[check(terminates)]
    #[requires(self == perm.ward())]
    #[ensures(val == (^perm)@)]
    #[ensures(resolve(perm@))]
    #[ensures(self == (^perm).ward())]
    pub unsafe fn set(&self, perm: Ghost<&mut Perm<PermCell<T>>>, val: T) {
        let _ = perm;
        unsafe {
            *self.0.get() = val;
        }
    }

    /// Replaces the contained value with `val`, and returns the old contained value.
    ///
    /// # Safety
    ///
    /// You must ensure that no other borrows to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PermCell#safety).
    #[trusted]
    #[check(terminates)]
    #[requires(self == perm.ward())]
    #[ensures(val == (^perm)@)]
    #[ensures(result == perm@)]
    #[ensures(self == (^perm).ward())]
    pub unsafe fn replace(&self, perm: Ghost<&mut Perm<PermCell<T>>>, val: T) -> T {
        let _ = perm;
        unsafe { core::ptr::replace(self.0.get(), val) }
    }

    /// Unwraps the value, consuming the cell.
    #[trusted]
    #[check(terminates)]
    #[requires(self == *perm.ward())]
    #[ensures(result == perm@)]
    pub fn into_inner(self, perm: Ghost<Box<Perm<PermCell<T>>>>) -> T {
        let _ = perm;
        self.0.into_inner()
    }

    /// Immutably borrows the wrapped value.
    ///
    /// The permission also acts as a guard, preventing writes to the underlying value
    /// while it is borrowed.
    ///
    /// # Safety
    ///
    /// You must ensure that no mutable borrow to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PermCell#safety).
    #[trusted]
    #[check(terminates)]
    #[requires(self == perm.ward())]
    #[ensures(*result == perm@)]
    pub unsafe fn borrow<'a>(&'a self, perm: Ghost<&'a Perm<PermCell<T>>>) -> &'a T {
        let _ = perm;
        unsafe { &*self.0.get() }
    }

    /// Mutably borrows the wrapped value.
    ///
    /// The permission also acts as a guard, preventing accesses to the underlying value
    /// while it is borrowed.
    ///
    /// # Safety
    ///
    /// You must ensure that no other borrows to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PermCell#safety).
    #[trusted]
    #[check(terminates)]
    #[requires(self == perm.ward())]
    #[ensures(self == (^perm).ward())]
    #[ensures(*result == perm@)]
    #[ensures(^result == (^perm)@)]
    pub unsafe fn borrow_mut<'a>(&'a self, perm: Ghost<&'a mut Perm<PermCell<T>>>) -> &'a mut T {
        let _ = perm;
        unsafe { &mut *self.0.get() }
    }
}

impl<T: Copy> PermCell<T> {
    /// Returns a copy of the contained value.
    ///
    /// # Safety
    ///
    /// You must ensure that no mutable borrow to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PermCell#safety).
    #[trusted]
    #[check(terminates)]
    #[requires(self == perm.ward())]
    #[ensures(result == (**perm)@)]
    pub unsafe fn get(&self, perm: Ghost<&Perm<PermCell<T>>>) -> T {
        let _ = perm;
        unsafe { *self.0.get() }
    }
}

impl<T> PermCell<T> {
    /// Returns a raw pointer to the underlying data in this cell.
    #[trusted]
    #[ensures(true)]
    pub fn as_ptr(&self) -> *mut T {
        self.0.get()
    }

    /// Returns a `&PermCell<T>` from a `&mut T`
    #[trusted]
    #[check(terminates)]
    #[ensures(result.0 == result.1.ward())]
    #[ensures(^t == (^result.1)@)]
    #[ensures(*t == result.1@)]
    pub fn from_mut(t: &mut T) -> (&PermCell<T>, Ghost<&mut Perm<PermCell<T>>>) {
        // SAFETY: `PermCell` is layout-compatible with `Cell` and `T` because it is `repr(transparent)`.
        // SAFETY: `&mut` ensures unique access
        let cell: &PermCell<T> = unsafe { &*(t as *mut T as *const Self) };
        let perm = Ghost::conjure();
        (cell, perm)
    }
}

impl<T: Default> PermCell<T> {
    /// Takes the value of the cell, leaving `Default::default()` in its place.
    ///
    /// # Safety
    ///
    /// You must ensure that no other borrows to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PermCell#safety).
    #[requires(self == perm.ward())]
    #[ensures(self == (^perm).ward())]
    #[ensures(result == perm@)]
    #[ensures(T::default.postcondition((), (^perm)@))]
    pub unsafe fn take(&self, perm: Ghost<&mut Perm<PermCell<T>>>) -> T {
        unsafe { self.replace(perm, T::default()) }
    }
}
