use crate::*;

mod private {
    /// Sealer for [`FnGhost`].
    pub trait _Sealed {}
}

/// Marker trait for functions that are [`check(ghost)`][check#ghost].
///
/// Right now, this is automatically implemented for `#[check(ghost)]` closures,
/// but not functions or methods.
#[cfg_attr(creusot, rustc_diagnostic_item = "fn_ghost_trait")]
pub trait FnGhost: private::_Sealed {}

// In non-creusot mode, FnGhost does nothing
#[cfg(not(creusot))]
impl<F> private::_Sealed for F {}
#[cfg(not(creusot))]
impl<F> FnGhost for F {}

/// Structure that implements [`FnGhost`].
///
/// This cannot be built by itself: instead, it automatically wraps
/// `#[check(ghost)]` closures.
#[doc(hidden)]
#[cfg_attr(creusot, rustc_diagnostic_item = "fn_ghost_ty")]
pub struct FnGhostWrapper<F>(F);

impl<F: Clone> Clone for FnGhostWrapper<F> {
    #[ensures(F::clone.postcondition((&self@,), result@))]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<F: Copy> Copy for FnGhostWrapper<F> {}

#[cfg(creusot)]
impl<I: ::std::marker::Tuple, F: FnOnce<I>> FnOnce<I> for FnGhostWrapper<F> {
    type Output = F::Output;

    #[requires(self.precondition(args))]
    #[ensures(self.postcondition_once(args, result))]
    #[trusted]
    #[check(ghost)]
    extern "rust-call" fn call_once(self, args: I) -> Self::Output {
        self.0.call_once(args)
    }
}
#[cfg(creusot)]
impl<I: ::std::marker::Tuple, F: FnMut<I>> FnMut<I> for FnGhostWrapper<F> {
    #[requires((*self).precondition(args))]
    #[ensures((*self).postcondition_mut(args, ^self, result))]
    #[trusted]
    #[check(ghost)]
    extern "rust-call" fn call_mut(&mut self, args: I) -> Self::Output {
        self.0.call_mut(args)
    }
}
#[cfg(creusot)]
impl<I: ::std::marker::Tuple, F: Fn<I>> Fn<I> for FnGhostWrapper<F> {
    #[requires((*self).precondition(args))]
    #[ensures((*self).postcondition(args, result))]
    #[trusted]
    #[check(ghost)]
    extern "rust-call" fn call(&self, args: I) -> Self::Output {
        self.0.call(args)
    }
}

impl<F> FnGhostWrapper<F> {
    /// DO NOT CALL THIS FUNCTION! This is an implementation detail, used by the `#[check(ghost)]`
    /// attribute.
    #[doc(hidden)]
    #[check(ghost)]
    #[ensures(result@ == f)]
    pub fn __new(f: F) -> Self {
        Self(f)
    }
}
impl<F> View for FnGhostWrapper<F> {
    type ViewTy = F;

    #[logic]
    fn view(self) -> Self::ViewTy {
        self.0
    }
}
#[cfg(creusot)]
impl<F> private::_Sealed for FnGhostWrapper<F> {}
#[cfg(creusot)]
impl<F> FnGhost for FnGhostWrapper<F> {}
