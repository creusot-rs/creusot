//! Shared mutation with a ghost token
//!
//! This allows a form of interior mutability, using [ghost](mod@crate::ghost) code to keep
//! track of the logical value.

#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{Ghost, logic::Id, *};
use ::std::{cell::UnsafeCell, marker::PhantomData};

/// Cell with ghost permissions
///
/// When writing/reading the cell, you need to explicitly pass a [`PermCellOwn`] object.
///
/// # Safety
///
/// When using Creusot to verify the code, all methods should be safe to call. Indeed,
/// Creusot ensures that every operation on the inner value uses the right [`PermCellOwn`] object
/// created by [`PermCell::new`], ensuring safety in a manner similar to [ghost_cell](https://docs.rs/ghost-cell/latest/ghost_cell/).
#[repr(transparent)]
#[opaque]
pub struct PermCell<T: ?Sized>(UnsafeCell<T>);

/// Token that represents the ownership of a [`PermCell`] object.
///
/// A `PermCellOwn` only exists in the ghost world, and it must be used in conjunction with
/// [`PermCell`] in order to read or write the value.
#[opaque]
pub struct PermCellOwn<T: ?Sized>(PhantomData<T>);

impl<T> View for PermCellOwn<T> {
    type ViewTy = T;

    #[logic(open, inline)]
    fn view(self) -> Self::ViewTy {
        *self.val()
    }
}

impl<T: ?Sized> Resolve for PermCellOwn<T> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
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

impl<T: Sized> Invariant for PermCellOwn<T> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        pearlite! { invariant::inv(self.val()) }
    }
}

impl<T: ?Sized> PermCellOwn<T> {
    /// Returns the logical identity of the cell.
    ///
    /// To use a [`PermCell`], this and [`PermCell::id`] must agree.
    #[logic(opaque)]
    pub fn id(self) -> Id {
        dead
    }

    /// Get the logical value.
    #[logic(opaque)]
    pub fn val<'a>(self) -> &'a T {
        dead
    }

    #[check(ghost)]
    #[ensures(*result == self.id())]
    pub fn id_ghost(&self) -> Ghost<Id> {
        snapshot!(self.id()).into_ghost()
    }

    /// If one owns two `PermCellOwn`s in ghost code, then they have different ids.
    #[trusted]
    #[check(ghost)]
    #[ensures(own1.id() != own2.id())]
    #[ensures(*own1 == ^own1)]
    #[allow(unused_variables)]
    pub fn disjoint_lemma(own1: &mut PermCellOwn<T>, own2: &PermCellOwn<T>) {}
}

impl<T> PermCell<T> {
    /// Creates a new `PermCell` containing the given value.
    #[trusted]
    #[check(terminates)]
    #[ensures(result.0.id() == result.1.id())]
    #[ensures((*result.1)@ == value)]
    pub fn new(value: T) -> (Self, Ghost<PermCellOwn<T>>) {
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
    #[requires(self.id() == perm.id())]
    #[ensures(val == (^perm)@)]
    #[ensures(resolve(perm@))]
    #[ensures(self.id() == (^perm).id())]
    pub unsafe fn set(&self, perm: Ghost<&mut PermCellOwn<T>>, val: T) {
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
    #[requires(self.id() == perm.id())]
    #[ensures(val == (^perm)@)]
    #[ensures(result == perm@)]
    #[ensures(self.id() == (^perm).id())]
    pub unsafe fn replace(&self, perm: Ghost<&mut PermCellOwn<T>>, val: T) -> T {
        let _ = perm;
        unsafe { std::ptr::replace(self.0.get(), val) }
    }

    /// Unwraps the value, consuming the cell.
    #[trusted]
    #[check(terminates)]
    #[requires(self.id() == perm.id())]
    #[ensures(result == perm@)]
    pub fn into_inner(self, perm: Ghost<PermCellOwn<T>>) -> T {
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
    #[requires(self.id() == perm.id())]
    #[ensures(*result == perm@)]
    pub unsafe fn borrow<'a>(&'a self, perm: Ghost<&'a PermCellOwn<T>>) -> &'a T {
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
    #[requires(self.id() == perm.id())]
    #[ensures(self.id() == (^perm).id())]
    #[ensures(*result == perm@)]
    #[ensures(^result == (^perm)@)]
    pub unsafe fn borrow_mut<'a>(&'a self, perm: Ghost<&'a mut PermCellOwn<T>>) -> &'a mut T {
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
    #[requires(self.id() == perm.id())]
    #[ensures(result == (**perm)@)]
    pub unsafe fn get(&self, perm: Ghost<&PermCellOwn<T>>) -> T {
        let _ = perm;
        unsafe { *self.0.get() }
    }
}

impl<T> PermCell<T> {
    /// Returns the logical identity of the cell.
    ///
    /// This is used to guarantee that a [`PermCellOwn`] is always used with the right [`PermCell`].
    #[logic(opaque)]
    pub fn id(self) -> Id {
        dead
    }

    #[check(ghost)]
    #[ensures(*result == self.id())]
    pub fn id_ghost(&self) -> Ghost<Id> {
        snapshot!(self.id()).into_ghost()
    }

    /// Returns a raw pointer to the underlying data in this cell.
    #[trusted]
    #[ensures(true)]
    pub fn as_ptr(&self) -> *mut T {
        self.0.get()
    }

    /// Returns a `&PermCell<T>` from a `&mut T`
    #[trusted]
    #[check(terminates)]
    #[ensures(result.0.id() == result.1.id())]
    #[ensures(^t == (^result.1)@)]
    #[ensures(*t == result.1@)]
    pub fn from_mut(t: &mut T) -> (&PermCell<T>, Ghost<&mut PermCellOwn<T>>) {
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
    #[requires(self.id() == perm.id())]
    #[ensures(self.id() == (^perm).id())]
    #[ensures(result == perm@)]
    #[ensures(T::default.postcondition((), (^perm)@))]
    pub unsafe fn take(&self, perm: Ghost<&mut PermCellOwn<T>>) -> T {
        unsafe { self.replace(perm, T::default()) }
    }
}
