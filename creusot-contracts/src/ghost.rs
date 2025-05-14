//! Definitions for ghost code
//!
//! Ghost code is code that will be erased during the normal compilation of the program.
//! To use ghost code in creusot, you must use the [`ghost!`] macro:
//!
//! ```
//! # use creusot_contracts::*;
//! let x: Ghost<i32> = ghost!(1);
//! ghost! {
//!     let y: i32 = *x;
//!     assert!(y == 1);
//! };
//! ```
//!
//! There are restrictions on the values that can enter/exit a `ghost!` block: see
//! [`Ghost`] and [`ghost!`] for more details.

#[cfg(creusot)]
use crate::resolve::structural_resolve;
use crate::{
    std::ops::{Deref, DerefMut},
    *,
};

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
#[cfg_attr(creusot, rustc_diagnostic_item = "ghost_ty")]
pub struct Ghost<T>(#[cfg(creusot)] T, #[cfg(not(creusot))] std::marker::PhantomData<T>);

impl<T: Clone> Clone for Ghost<T> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        #[cfg(creusot)]
        {
            Self(self.0.clone())
        }
        #[cfg(not(creusot))]
        {
            Self(std::marker::PhantomData)
        }
    }
}

impl<T> Deref for Ghost<T> {
    type Target = T;

    /// This function can only be called in `ghost!` context
    #[cfg_attr(creusot, rustc_diagnostic_item = "ghost_deref")]
    #[pure]
    #[ensures((*self).inner_logic() == *result)]
    fn deref(&self) -> &Self::Target {
        #[cfg(creusot)]
        {
            &self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }
}
impl<T> DerefMut for Ghost<T> {
    /// This function can only be called in `ghost!` context
    #[cfg_attr(creusot, rustc_diagnostic_item = "ghost_deref_mut")]
    #[pure]
    #[ensures(*result == (*self).inner_logic())]
    #[ensures(^result == (^self).inner_logic())]
    fn deref_mut(&mut self) -> &mut Self::Target {
        #[cfg(creusot)]
        {
            &mut self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }
}

impl<T: View> View for Ghost<T> {
    type ViewTy = T::ViewTy;
    #[logic]
    #[open]
    fn view(self) -> Self::ViewTy {
        (*self).view()
    }
}

impl<T> Invariant for Ghost<T> {
    #[predicate(prophetic)]
    #[open]
    fn invariant(self) -> bool {
        inv(self.inner_logic())
    }
}

impl<T> Resolve for Ghost<T> {
    #[open]
    #[predicate(prophetic)]
    fn resolve(self) -> bool {
        resolve(&self.inner_logic())
    }

    #[logic(prophetic)]
    #[open(self)]
    #[requires(structural_resolve(self))]
    #[ensures((*self).resolve())]
    fn resolve_coherence(&self) {}
}

impl<T> Ghost<T> {
    /// Transforms a `&Ghost<T>` into `Ghost<&T>`.
    #[pure]
    #[ensures(**result == **self)]
    pub fn borrow(&self) -> Ghost<&T> {
        #[cfg(creusot)]
        {
            Ghost(&self.0)
        }
        #[cfg(not(creusot))]
        {
            Ghost(std::marker::PhantomData)
        }
    }

    /// Transforms a `&mut Ghost<T>` into a `Ghost<&mut T>`.
    #[pure]
    #[ensures(*result.inner_logic() == (*self).inner_logic())]
    #[ensures(^result.inner_logic() == (^self).inner_logic())]
    pub fn borrow_mut(&mut self) -> Ghost<&mut T> {
        #[cfg(creusot)]
        {
            Ghost(&mut self.0)
        }
        #[cfg(not(creusot))]
        {
            Ghost(std::marker::PhantomData)
        }
    }

    /// Conjures a `Ghost<T>` out of thin air.
    ///
    /// This would be unsound in verified code, hence the `false` precondition.
    /// This function is nevertheless useful to create a `Ghost` in "trusted"
    /// contexts, when axiomatizing an API that is believed to be sound for
    /// external reasons.
    #[pure]
    #[requires(false)]
    pub fn conjure() -> Self {
        #[cfg(creusot)]
        {
            panic!()
        }
        #[cfg(not(creusot))]
        {
            Ghost(std::marker::PhantomData)
        }
    }

    // Internal function to easily create a `Ghost` in non-creusot mode.
    #[cfg(not(creusot))]
    #[doc(hidden)]
    pub fn from_fn(_: impl FnOnce() -> T) -> Self {
        Ghost(std::marker::PhantomData)
    }
}

impl<T> Ghost<T> {
    /// Creates a new ghost variable.
    ///
    /// This function can only be called in `ghost!` code.
    #[pure]
    #[ensures(*result == x)]
    #[cfg_attr(creusot, rustc_diagnostic_item = "ghost_new")]
    pub fn new(x: T) -> Self {
        #[cfg(creusot)]
        {
            Self(x)
        }
        #[cfg(not(creusot))]
        {
            let _ = x;
            Self(std::marker::PhantomData)
        }
    }

    #[logic]
    #[open(self)]
    #[ensures(*result == x)]
    pub fn new_logic(x: T) -> Self {
        Self(x)
    }

    /// Returns the inner value of the `Ghost`.
    ///
    /// This function can only be called in `ghost!` context.
    #[pure]
    #[ensures(result == *self)]
    #[cfg_attr(creusot, rustc_diagnostic_item = "ghost_into_inner")]
    pub fn into_inner(self) -> T {
        #[cfg(creusot)]
        {
            self.0
        }
        #[cfg(not(creusot))]
        {
            panic!()
        }
    }

    /// Returns the inner value of the `Ghost`.
    ///
    /// You should prefer the dereference operator `*` instead.
    #[logic]
    #[open]
    #[rustc_diagnostic_item = "ghost_inner_logic"]
    pub fn inner_logic(self) -> T {
        self.0
    }
}

impl<T, U> Ghost<(T, U)> {
    #[pure]
    #[trusted]
    #[ensures(*self == (*result.0, *result.1))]
    pub fn split(self) -> (Ghost<T>, Ghost<U>) {
        (Ghost::conjure(), Ghost::conjure())
    }
}
