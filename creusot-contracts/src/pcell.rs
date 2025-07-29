//! Shared mutation with a ghost token
//!
//! This allows a form of interior mutability, using [ghost](mod@crate::ghost) code to keep
//! track of the logical value.

#[cfg(creusot)]
use crate::logic::Id;

use crate::{Ghost, *};
use ::std::{cell::UnsafeCell, marker::PhantomData};

/// A "permission" cell allowing interior mutability via a ghost token.
///
/// When writing/reading the cell, you need to explicitely pass a [`PCellOwn`] object.
///
/// # Safety
///
/// When using Creusot to verify the code, all methods should be safe to call. Indeed,
/// Creusot ensures that every operation on the inner value uses the right [`PCellOwn`] object
/// created by [`PCell::new`], ensuring safety in a manner similar to [ghost_cell](https://docs.rs/ghost-cell/latest/ghost_cell/).
#[repr(transparent)]
pub struct PCell<T: ?Sized>(UnsafeCell<T>);

/// Token that represents the ownership of a [`PCell`] object.
///
/// A `PCellOwn` only exists in the ghost world, and it must be used in conjunction with
/// [`PCell`] in order to read or write the value.
pub struct PCellOwn<T: ?Sized>(PhantomData<T>);

impl<T> View for PCellOwn<T> {
    type ViewTy = T;

    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        *self.val()
    }
}

impl<T: ?Sized> Resolve for PCellOwn<T> {
    #[open]
    #[logic(prophetic)]
    fn resolve(self) -> bool {
        resolve(self.val())
    }

    #[trusted]
    #[logic(prophetic)]
    #[requires(inv(self))]
    #[requires(structural_resolve(self))]
    #[ensures(self.resolve())]
    fn resolve_coherence(self) {}
}

impl<T: Sized> Invariant for PCellOwn<T> {
    #[logic(prophetic)]
    #[open]
    #[creusot::trusted_ignore_structural_inv]
    #[creusot::trusted_is_tyinv_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { invariant::inv(self.val()) }
    }
}

impl<T: ?Sized> PCellOwn<T> {
    /// Returns the logical identity of the cell.
    ///
    /// To use a [`Pcell`], this and [`PCell::id`] must agree.
    #[logic]
    #[trusted]
    pub fn id(self) -> Id {
        dead
    }

    /// Get the logical value.
    #[logic]
    #[trusted]
    pub fn val<'a>(self) -> &'a T {
        dead
    }

    /// If one owns two `PCellOwn`s in ghost code, then they have different ids.
    #[trusted]
    #[pure]
    #[ensures(own1.id() != own2.id())]
    #[ensures(*own1 == ^own1)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(own1: &mut PCellOwn<T>, own2: &PCellOwn<T>) {}
}

impl<T> PCell<T> {
    /// Creates a new `PCell` containing the given value.
    #[trusted]
    #[ensures(result.0.id() == result.1.id())]
    #[ensures((*result.1)@ == value)]
    pub fn new(value: T) -> (Self, Ghost<PCellOwn<T>>) {
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
    /// [type documentation](PCell).
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(val == (^perm.inner_logic())@)]
    #[ensures(resolve(&(*perm.inner_logic())@))]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    pub unsafe fn set(&self, perm: Ghost<&mut PCellOwn<T>>, val: T) {
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
    /// [type documentation](PCell).
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(val == (^perm.inner_logic())@)]
    #[ensures(result == (*perm.inner_logic())@)]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    pub unsafe fn replace(&self, perm: Ghost<&mut PCellOwn<T>>, val: T) -> T {
        let _ = perm;
        unsafe { std::ptr::replace(self.0.get(), val) }
    }

    /// Unwraps the value, consuming the cell.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(result == perm@)]
    pub fn into_inner(self, perm: Ghost<PCellOwn<T>>) -> T {
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
    /// [type documentation](PCell).
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(*result == perm@)]
    pub unsafe fn borrow<'a>(&'a self, perm: Ghost<&'a PCellOwn<T>>) -> &'a T {
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
    /// [type documentation](PCell).
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    #[ensures(*result == (*perm.inner_logic())@)]
    #[ensures(^result == (^perm.inner_logic())@)]
    pub unsafe fn borrow_mut<'a>(&'a self, perm: Ghost<&'a mut PCellOwn<T>>) -> &'a mut T {
        let _ = perm;
        unsafe { &mut *self.0.get() }
    }
}

impl<T: Copy> PCell<T> {
    /// Returns a copy of the contained value.
    ///
    /// # Safety
    ///
    /// You must ensure that no mutable borrow to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PCell).
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(result == (**perm)@)]
    pub unsafe fn get(&self, perm: Ghost<&PCellOwn<T>>) -> T {
        let _ = perm;
        unsafe { *self.0.get() }
    }
}

impl<T> PCell<T> {
    /// Returns the logical identity of the cell.
    ///
    /// This is used to guarantee that a [`PCellOwn`] is always used with the right [`PCell`].
    #[logic]
    #[trusted]
    pub fn id(self) -> Id {
        dead
    }

    /// Returns a raw pointer to the underlying data in this cell.
    #[trusted]
    #[ensures(true)]
    pub fn as_ptr(&self) -> *mut T {
        self.0.get()
    }

    /// Returns a `&PCell<T>` from a `&mut T`
    #[trusted]
    #[ensures(result.0.id() == result.1.inner_logic().id())]
    #[ensures(^t == (^result.1.inner_logic())@)]
    #[ensures(*t == (*result.1.inner_logic())@)]
    pub fn from_mut(t: &mut T) -> (&PCell<T>, Ghost<&mut PCellOwn<T>>) {
        // SAFETY: `PCell` is layout-compatible with `Cell` and `T` because it is `repr(transparent)`.
        // SAFETY: `&mut` ensures unique access
        let cell: &PCell<T> = unsafe { &*(t as *mut T as *const Self) };
        let perm = Ghost::conjure();
        (cell, perm)
    }
}

impl<T: Default> PCell<T> {
    /// Takes the value of the cell, leaving `Default::default()` in its place.
    ///
    /// # Safety
    ///
    /// You must ensure that no other borrows to the inner value of `self` exists when calling
    /// this function.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](PCell).
    #[requires(self.id() == perm.id())]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    #[ensures(result == (*perm.inner_logic())@)]
    #[ensures(T::default.postcondition((), (^perm.inner_logic())@))]
    pub unsafe fn take(&self, perm: Ghost<&mut PCellOwn<T>>) -> T {
        unsafe { self.replace(perm, T::default()) }
    }
}
