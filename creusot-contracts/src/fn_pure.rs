use crate::*;

mod private {
    /// Sealer for [`FnPure`].
    pub trait _Sealed {}
}

/// Marker trait for functions that are [`pure`].
///
/// To create such a function, the easiest way is to use [`clos_pure`].
pub trait FnPure: private::_Sealed {}

/// Structure that implements [`FnPure`].
///
/// This cannot be built by itself: instead, you should use the [`clos_pure`] macro.
#[doc(hidden)]
pub struct FnPureWrapper<F>(F);

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

impl<I: ::std::marker::Tuple, F: FnMut<I>> FnMut<I> for FnPureWrapper<F> {
    #[requires((*self).precondition(args))]
    #[ensures((*self).postcondition_mut(args, ^self, result))]
    #[trusted]
    #[pure]
    extern "rust-call" fn call_mut(&mut self, args: I) -> Self::Output {
        self.0.call_mut(args)
    }
}

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
    /// DO NOT CALL THIS FUNCTION! This is an implementation detail, required to make
    /// `clos_pure` work.
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
    #[open(self)]
    fn view(self) -> Self::ViewTy {
        self.0
    }
}
impl<F> private::_Sealed for FnPureWrapper<F> {}
impl<F> FnPure for FnPureWrapper<F> {}

/// Create a closure marked with [`pure`], that will implement [`FnPure`].
///
/// # Example
///
/// ```rust
/// # use creusot_contracts::*;
///
/// #[pure]
/// #[requires(f.precondition((x,)))]
/// #[ensures(f.postcondition_once((x,), result))]
/// fn call_pure(f: Fn() -> i32 + FnPure, x: i32) -> i32 { f(x) }
/// let f = clos_pure!(|x: i32| x + 1);
/// let y = call_pure(f);
/// assert!(y == 3);
/// ```
#[macro_export]
macro_rules! clos_pure {
    ($c:expr) => {
        $crate::fn_pure::FnPureWrapper::__new(
            #[pure]
            $c,
        )
    };
}
