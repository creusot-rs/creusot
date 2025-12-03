//! Definitions for ghost code
//!
//! Ghost code is code that will be erased during the normal compilation of the program.
//! To use ghost code in creusot, you must use the [`ghost!`] macro:
//!
//! ```
//! # use creusot_contracts::prelude::*;
//! let x: Ghost<i32> = ghost!(1);
//! ghost! {
//!     let y: i32 = *x;
//!     assert!(y == 1);
//! };
//! ```
//!
//! There are restrictions on the values that can enter/exit a `ghost!` block: see
//! [`Ghost`] and [`ghost!`] for more details.

use crate::{logic::ops::Fin, prelude::*};
use std::{
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

mod fn_ghost;
pub mod local_invariant;
mod ptr_own;
pub mod resource;
pub use fn_ghost::{FnGhost, FnGhostWrapper};
pub use ptr_own::PtrOwn;

/// A type that can be used in [`ghost!`] context.
///
/// This type may be used to make more complicated proofs possible. In particular, some
/// proof may need a notion of non-duplicable token to carry around.
///
/// Conceptually, a `Ghost<T>` is an object of type `T` that resides in a special "ghost"
/// heap. This heap is inaccessible from normal code, and `Ghost` values cannot be used
/// to influence the behavior of normal code.
///
/// This box can be accessed in a [`ghost!`] block:
/// ```compile_fail
/// let b: Ghost<i32> = Ghost::new(1);
/// ghost! {
///     let value: i32 = b.into_inner();
///     // use value here
/// }
/// let value: i32 = b.into_inner(); // compile error !
/// ```
#[opaque]
#[intrinsic("ghost")]

pub struct Ghost<T: ?Sized>(PhantomData<T>);

impl<T: Copy> Copy for Ghost<T> {}

// FIXME: we would like to have an instance that does not require T: Copy, but it would
// require the underlying clone instance to be #[check(ghost)], which we cannot require in general
impl<T: Clone + Copy> Clone for Ghost<T> {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        ghost!(**self)
    }
}

impl<T: ?Sized> Deref for Ghost<T> {
    type Target = T;

    /// This function can only be called in `ghost!` context
    #[trusted]
    #[check(ghost)]
    #[requires(false)] // If called from generic context, false precondition
    #[ensures(result == &**self)]
    #[intrinsic("ghost_deref")]
    fn deref(&self) -> &Self::Target {
        panic!()
    }
}
impl<T: ?Sized> DerefMut for Ghost<T> {
    /// This function can only be called in `ghost!` context
    #[trusted]
    #[check(ghost)]
    #[requires(false)] // If called from generic context, false precondition
    #[ensures(result == &mut **self)]
    #[intrinsic("ghost_deref_mut")]
    fn deref_mut(&mut self) -> &mut Self::Target {
        panic!()
    }
}

impl<T: ?Sized + Fin> Fin for Ghost<T> {
    type Target = T::Target;

    #[logic(open, prophetic, inline)]
    fn fin<'a>(self) -> &'a Self::Target {
        pearlite! { &^*self }
    }
}

impl<T: ?Sized> Invariant for Ghost<T> {
    #[logic(open, prophetic, inline)]
    #[creusot::trusted_trivial_if_param_trivial]
    fn invariant(self) -> bool {
        inv(*self)
    }
}

impl<T: ?Sized> Ghost<T> {
    /// Transforms a `&Ghost<T>` into `Ghost<&T>`
    #[trusted]
    #[erasure(_)]
    #[check(ghost)]
    #[ensures(**result == **self)]
    pub fn borrow(&self) -> Ghost<&T> {
        Ghost::conjure()
    }

    /// Transforms a `&mut Ghost<T>` into a `Ghost<&mut T>`.
    #[trusted]
    #[erasure(_)]
    #[check(ghost)]
    #[ensures(*result == &mut **self)]
    pub fn borrow_mut(&mut self) -> Ghost<&mut T> {
        Ghost::conjure()
    }

    /// Conjures a `Ghost<T>` out of thin air.
    ///
    /// This would be unsound in verified code, hence the `false` precondition.
    /// This function is nevertheless useful to create a `Ghost` in "trusted"
    /// contexts, when axiomatizing an API that is believed to be sound for
    /// external reasons.
    #[trusted]
    #[erasure(_)]
    #[check(ghost)]
    #[requires(false)]
    pub fn conjure() -> Self {
        Ghost(PhantomData)
    }

    // Internal function to easily create a `Ghost` in non-creusot mode.
    #[cfg(not(creusot))]
    #[doc(hidden)]
    pub fn from_fn(_: impl FnOnce() -> T) -> Self {
        Ghost::conjure()
    }
}

impl<T: ?Sized> Ghost<T> {
    /// Creates a new ghost variable.
    ///
    /// This function can only be called in `ghost!` code.
    #[trusted]
    #[check(ghost)]
    #[ensures(*result == x)]
    #[intrinsic("ghost_new")]
    pub fn new(x: T) -> Self
    where
        T: Sized,
    {
        let _ = x;
        panic!()
    }

    #[trusted]
    #[logic(opaque)]
    #[ensures(*result == x)]
    pub fn new_logic(x: T) -> Self {
        dead
    }

    /// Returns the inner value of the `Ghost`.
    ///
    /// This function can only be called in `ghost!` context.
    #[trusted]
    #[check(ghost)]
    #[ensures(result == *self)]
    #[intrinsic("ghost_into_inner")]
    pub fn into_inner(self) -> T
    where
        T: Sized,
    {
        panic!()
    }

    /// Returns the inner value of the `Ghost`.
    ///
    /// This does not require `T` to be `Sized`.
    ///
    /// This function can only be called in `ghost!` context.
    #[trusted]
    #[check(ghost)]
    #[ensures(*result == *self)]
    #[intrinsic("ghost_into_inner_unsized")]
    pub fn into_inner_unsized(self) -> Box<T> {
        panic!()
    }

    /// Returns the inner value of the `Ghost`.
    ///
    /// You should prefer the dereference operator `*` instead.
    #[logic]
    #[builtin("identity")]
    pub fn inner_logic(self) -> T
    where
        T: Sized,
    {
        dead
    }
}

impl<T, U: ?Sized> Ghost<(T, U)> {
    #[check(ghost)]
    #[trusted]
    #[erasure(_)]
    #[ensures((*self).0 == *result.0)]
    #[ensures((*self).1 == *result.1)]
    pub fn split(self) -> (Ghost<T>, Ghost<U>) {
        (Ghost::conjure(), Ghost::conjure())
    }
}

/// A marker trait for types that can be extracted from snapshots in ghost code.
/// These are type that only contain plain data and whose onership does not convey
/// any additional information.
///
/// For example, Booleans and integers are plain, but references are not, be they
/// mutable or not. Indeed, the ownership of a shared reference can be used to deduce
/// facts, for example with `PtrOwn::disjoint_lemma`.
#[trusted]
pub trait Plain: Copy {}

#[trusted]
impl Plain for bool {}

#[trusted]
impl<T> Plain for *const T {}

#[trusted]
impl<T> Plain for *mut T {}
