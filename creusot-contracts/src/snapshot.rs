//! Definition of [`Snapshot`]

use crate::*;

#[cfg(creusot)]
use crate::std::ops::Deref;

/// A copyable snapshot, usable in pearlite.
///
/// The `Snapshot` type contains the logical value of some data, in a purely immutable way.
/// It is zero sized.
///
/// Creating a snapshot does _not_ move the ownership of a value.
///
/// # Pearlite syntax
///
/// In executable code, you may create a snapshot with the [`snapshot!`] macro. Inside
/// this macro, you may write _pearlite_ code; this code will not run during the normal
/// execution of the program.
///
/// ## Example
///
/// ```
/// # use creusot_contracts::{*, logic::Mapping};
/// let x: Snapshot<Int> = snapshot!(1);
/// let m: Snapshot<Mapping<Int, Int>> = snapshot!(|x| x + 1);
/// ```
#[trusted]
#[cfg_attr(creusot, rustc_diagnostic_item = "snapshot_ty", creusot::builtins = "")]
pub struct Snapshot<T: ?Sized>(std::marker::PhantomData<T>);

#[cfg(creusot)]
impl<T: ?Sized> Deref for Snapshot<T> {
    type Target = T;

    #[trusted]
    #[rustc_diagnostic_item = "snapshot_deref"]
    #[creusot::builtins = "identity"]
    fn deref(&self) -> &Self::Target {
        panic!()
    }
}

impl<T: View + ?Sized> View for Snapshot<T> {
    type ViewTy = T::ViewTy;

    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        self.deref().view()
    }
}

impl<T: ?Sized> Clone for Snapshot<T> {
    #[pure]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for Snapshot<T> {}

impl<T: ?Sized> Snapshot<T> {
    /// Create a new snapshot in logic code.
    #[trusted]
    #[logic]
    #[creusot::builtins = "identity"]
    pub fn new(value: T) -> Snapshot<T> {
        let _ = value;
        dead
    }

    /// Get the value of the snapshot.
    ///
    /// When possible, you should instead use the dereference operator.
    ///
    /// # Example
    /// ```
    /// # use creusot_contracts::*;
    /// let x = snapshot!(1);
    /// proof_assert!(x.inner() == 1);
    /// proof_assert!(*x == 1); // prefer this
    /// ```
    #[trusted]
    #[logic]
    #[creusot::builtins = "identity"]
    pub fn inner(self) -> T
    where
        T: Sized, // TODO: don't require T: Sized here. Problem: return type is T.
    {
        dead
    }

    /// Internal function used in the `snapshot!` macro.
    #[doc(hidden)]
    #[cfg(not(creusot))]
    pub fn from_fn(_: fn() -> T) -> Self {
        Snapshot(std::marker::PhantomData)
    }
}
