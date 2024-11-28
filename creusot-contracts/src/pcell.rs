//! Shared mutation with a ghost token
//!
//! This allows a form of interior mutability, using [ghost](mod@crate::ghost) code to keep
//! track of the logical value.

use crate::{GhostBox, *};
use ::std::{cell::UnsafeCell, marker::PhantomData};

/// A "permission" cell allowing interior mutability via a ghost token.
///
/// When writing/reading the cell, you need to explicitely pass a [`PCellOwn`] object.
#[repr(transparent)]
pub struct PCell<T: ?Sized>(UnsafeCell<T>);

/// The id of a [`PCell`].
#[trusted]
#[allow(dead_code)]
pub struct Id(PhantomData<()>);

/// Token that represents the ownership of a [`PCell`] object.
///
/// A `PCellOwn` only exists in the ghost world, and it must be used in conjunction with
/// [`PCell`] in order to read or write the value.
#[trusted]
pub struct PCellOwn<T: ?Sized>(PhantomData<T>);

impl<T> View for PCellOwn<T> {
    type ViewTy = T;

    #[logic]
    #[trusted]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

impl<T> PCellOwn<T>
where
    T: ?Sized,
{
    /// Returns the logical identity of the cell.
    ///
    /// To use a [`Pcell`], this and [`PCell::id`] must agree.
    #[logic]
    #[trusted]
    pub fn id(self) -> Id {
        dead
    }
}

impl<T> PCellOwn<T> {
    /// Get the logical value.
    #[logic]
    #[open]
    pub fn val(self) -> T {
        self.view()
    }
}

impl<T> PCell<T> {
    /// Creates a new `PCell` containing the given value.
    #[trusted]
    #[ensures(result.0.id() == result.1.id())]
    #[ensures((*result.1)@ == value)]
    #[allow(unreachable_code)]
    pub fn new(value: T) -> (Self, GhostBox<PCellOwn<T>>) {
        let this = Self(UnsafeCell::new(value));
        let perm = ghost!(panic!());
        (this, perm)
    }

    /// Sets the contained value.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(val == (^perm.inner_logic()).val())]
    #[ensures(resolve(&(*perm.inner_logic()).val()))]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    pub fn set(&self, perm: GhostBox<&mut PCellOwn<T>>, val: T) {
        let _ = perm;
        unsafe {
            *self.0.get() = val;
        }
    }

    /// Replaces the contained value with `val`, and returns the old contained value.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(val == (^perm.inner_logic()).val())]
    #[ensures(result == (*perm.inner_logic()).val())]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    pub fn replace(&self, perm: GhostBox<&mut PCellOwn<T>>, val: T) -> T {
        let _ = perm;
        unsafe { std::ptr::replace(self.0.get(), val) }
    }

    /// Unwraps the value, consuming the cell.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(result == perm.val())]
    pub fn into_inner(self, perm: GhostBox<PCellOwn<T>>) -> T {
        let _ = perm;
        self.0.into_inner()
    }

    /// Immutably borrows the wrapped value.
    ///
    /// The permission also acts as a guard, preventing writes to the underlying value
    /// while it is borrowed.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(*result == perm.val())]
    pub fn borrow<'a>(&'a self, perm: GhostBox<&'a PCellOwn<T>>) -> &'a T {
        let _ = perm;
        unsafe { &*self.0.get() }
    }

    /// Mutably borrows the wrapped value.
    ///
    /// The permission also acts as a guard, preventing accesses to the underlying value
    /// while it is borrowed.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    #[ensures(*result == (*perm.inner_logic()).val())]
    #[ensures(^result == (^perm.inner_logic()).val())]
    pub fn borrow_mut<'a>(&'a self, perm: GhostBox<&'a mut PCellOwn<T>>) -> &'a mut T {
        let _ = perm;
        unsafe { &mut *self.0.get() }
    }
}

impl<T> PCell<T>
where
    T: Copy,
{
    /// Returns a copy of the contained value.
    #[trusted]
    #[requires(self.id() == perm.id())]
    #[ensures(result == (**perm)@)]
    pub fn get(&self, perm: GhostBox<&PCellOwn<T>>) -> T {
        let _ = perm;
        unsafe { *self.0.get() }
    }
}

impl<T> PCell<T>
where
    T: ?Sized,
{
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
    // TODO: #[ensures(^t == (^result.1.inner_logic()).val())]
    #[allow(unreachable_code)]
    pub fn from_mut(t: &mut T) -> (&PCell<T>, GhostBox<&mut PCellOwn<T>>) {
        // SAFETY: `PCell` is layout-compatible with `Cell` and `T` because it is `repr(transparent)`.
        // SAFETY: `&mut` ensures unique access
        let cell: &PCell<T> = unsafe { &*(t as *mut T as *const Self) };
        let perm = ghost!(panic!());
        (cell, perm)
    }
}

impl<T> PCell<T>
where
    T: crate::std::default::Default,
{
    /// Takes the value of the cell, leaving `Default::default()` in its place.
    #[requires(self.id() == perm.id())]
    #[ensures(self.id() == (^perm.inner_logic()).id())]
    #[ensures(result == (*perm.inner_logic()).val())]
    #[ensures((^perm.inner_logic()).val().is_default())]
    pub fn take(&self, perm: GhostBox<&mut PCellOwn<T>>) -> T {
        self.replace(perm, T::default())
    }
}
