use crate::*;

mod private {
    /// Sealer for [`FnPure`].
    pub trait _Sealed {}
}

/// Marker trait for functions that are [`pure`].
///
/// Right now, this is automatically implemented for `#[pure]` closures, but not
/// functions or methods.
#[cfg_attr(creusot, rustc_diagnostic_item = "fn_pure_trait")]
pub trait FnPure: private::_Sealed {}

// In non-creusot mode, FnPure does nothing
#[cfg(not(creusot))]
impl<F> private::_Sealed for F {}
#[cfg(not(creusot))]
impl<F> FnPure for F {}

/// Structure that implements [`FnPure`].
///
/// This cannot be built by itself: instead, it automatically wraps `#[pure]` closures.
#[doc(hidden)]
#[cfg_attr(creusot, rustc_diagnostic_item = "fn_pure_ty")]
pub struct FnPureWrapper<F>(F);

impl<F: Clone> Clone for FnPureWrapper<F> {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
impl<F: Copy> Copy for FnPureWrapper<F> {}

#[cfg(creusot)]
impl<I: ::std::marker::Tuple, F: FnOnce<I>> FnOnce<I> for FnPureWrapper<F> {
    type Output = F::Output;

    #[requires(self.precondition(args))]
    #[ensures(self.postcondition_once(args, result))]
    #[trusted]
    #[pure]
    extern "rust-call" fn call_once(self, args: I) -> Self::Output {
        self.0.call_once(args)
    }
}
#[cfg(creusot)]
impl<I: ::std::marker::Tuple, F: FnMut<I>> FnMut<I> for FnPureWrapper<F> {
    #[requires((*self).precondition(args))]
    #[ensures((*self).postcondition_mut(args, ^self, result))]
    #[trusted]
    #[pure]
    extern "rust-call" fn call_mut(&mut self, args: I) -> Self::Output {
        self.0.call_mut(args)
    }
}
#[cfg(creusot)]
impl<I: ::std::marker::Tuple, F: Fn<I>> Fn<I> for FnPureWrapper<F> {
    #[requires((*self).precondition(args))]
    #[ensures((*self).postcondition(args, result))]
    #[trusted]
    #[pure]
    extern "rust-call" fn call(&self, args: I) -> Self::Output {
        self.0.call(args)
    }
}

impl<F> FnPureWrapper<F> {
    /// DO NOT CALL THIS FUNCTION! This is an implementation detail, used by the `#[pure]`
    /// attribute.
    #[doc(hidden)]
    #[pure]
    #[ensures(result@ == f)]
    pub fn __new(f: F) -> Self {
        Self(f)
    }
}
impl<F> View for FnPureWrapper<F> {
    type ViewTy = F;
    #[logic]
    fn view(self) -> Self::ViewTy {
        self.0
    }
}
#[cfg(creusot)]
impl<F> private::_Sealed for FnPureWrapper<F> {}
#[cfg(creusot)]
impl<F> FnPure for FnPureWrapper<F> {}
