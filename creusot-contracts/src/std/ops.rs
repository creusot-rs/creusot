use crate::*;
use ::std::convert::Infallible;
#[cfg(feature = "nightly")]
use ::std::marker::Tuple;
pub use ::std::ops::*;

// Note: we should NOT give a generic extern spec for Deref::deref, since this
// method is an exception being used both as a logic function and as a program
// function. See #1235.

/// `FnOnceExt` is an extension trait for the `FnOnce` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(feature = "nightly")]
pub trait FnOnceExt<Args: Tuple> {
    type Output;

    #[logic(prophetic)]
    fn precondition(self, a: Args) -> bool;

    #[logic(prophetic)]
    fn postcondition_once(self, a: Args, res: Self::Output) -> bool;
}

#[cfg(not(feature = "nightly"))]
pub trait FnOnceExt<Args> {
    type Output;
}

/// `FnMutExt` is an extension trait for the `FnMut` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(feature = "nightly")]
pub trait FnMutExt<Args: Tuple>: FnOnceExt<Args> {
    #[logic(prophetic)]
    fn postcondition_mut(self, _: Args, _: Self, _: Self::Output) -> bool;

    #[logic(prophetic)]
    fn hist_inv(self, _: Self) -> bool;

    #[law]
    #[requires(self.postcondition_mut(args, res_state, res))]
    #[ensures(self.hist_inv(res_state))]
    fn postcondition_mut_hist_inv(self, args: Args, res_state: Self, res: Self::Output);

    #[law]
    #[ensures(self.hist_inv(self))]
    fn hist_inv_refl(self);

    #[law]
    #[requires(self.hist_inv(b))]
    #[requires(b.hist_inv(c))]
    #[ensures(self.hist_inv(c))]
    fn hist_inv_trans(self, b: Self, c: Self);

    #[law]
    #[ensures(self.postcondition_once(args, res) ==
              exists<res_state: Self> self.postcondition_mut(args, res_state, res) && resolve(res_state))]
    fn fn_mut_once(self, args: Args, res: Self::Output);
}

#[cfg(not(feature = "nightly"))]
pub trait FnMutExt<Args>: FnOnceExt<Args> {}

/// `FnExt` is an extension trait for the `Fn` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(feature = "nightly")]
pub trait FnExt<Args: Tuple>: FnMutExt<Args> {
    #[logic(prophetic)]
    fn postcondition(self, _: Args, _: Self::Output) -> bool;

    #[law]
    #[ensures(self.postcondition_mut(args, res_state, res) == (self.postcondition(args, res) && self == res_state))]
    fn fn_mut(self, args: Args, res_state: Self, res: Self::Output);

    #[law]
    #[ensures(self.postcondition_once(args, res) == (self.postcondition(args, res) && resolve(&self)))]
    fn fn_once(self, args: Args, res: Self::Output);

    #[law]
    #[ensures(self.hist_inv(res_state) == (self == res_state))]
    fn fn_hist_inv(self, res_state: Self);
}

/// `FnExt` is an extension trait for the `Fn` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(not(feature = "nightly"))]
pub trait FnExt<Args>: FnMutExt<Args> {}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: ?Sized + FnOnce<Args>> FnOnceExt<Args> for F {
    type Output = <Self as FnOnce<Args>>::Output;

    #[trusted]
    #[logic(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_once_impl_precond"]
    fn precondition(self, args: Args) -> bool {
        dead
    }

    #[trusted]
    #[logic(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_once_impl_postcond"]
    fn postcondition_once(self, args: Args, result: Self::Output) -> bool {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: ?Sized + FnMut<Args>> FnMutExt<Args> for F {
    #[trusted]
    #[logic(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_mut_impl_postcond"]
    fn postcondition_mut(self, args: Args, result_state: Self, result: Self::Output) -> bool {
        dead
    }

    #[trusted]
    #[logic(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_mut_impl_hist_inv"]
    fn hist_inv(self, result_state: Self) -> bool {
        dead
    }

    #[trusted]
    #[law]
    #[requires((*&self).postcondition_mut(args, *&res_state, res))]
    #[ensures((*&self).hist_inv(*&res_state))]
    fn postcondition_mut_hist_inv(self, args: Args, res_state: Self, res: Self::Output) {}

    #[trusted]
    #[law]
    #[ensures((*&self).hist_inv(*&self))]
    fn hist_inv_refl(self) {}

    #[trusted]
    #[law]
    #[requires((*&self).hist_inv(*&b))]
    #[requires((*&b).hist_inv(*&c))]
    #[ensures((*&self).hist_inv(*&c))]
    fn hist_inv_trans(self, b: Self, c: Self) {}

    #[law]
    #[trusted]
    #[ensures((*&self).postcondition_once(args, res) ==
              exists<res_state: Self> (*&self).postcondition_mut(args, res_state, res) && resolve(res_state))]
    fn fn_mut_once(self, args: Args, res: Self::Output) {}
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: ?Sized + Fn<Args>> FnExt<Args> for F {
    #[trusted]
    #[logic]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_impl_postcond"]
    fn postcondition(self, args: Args, result: Self::Output) -> bool {
        dead
    }

    #[law]
    #[trusted]
    #[ensures((*&self).postcondition_mut(args, *&res_state, res) == ((*&self).postcondition(args, res) && *&self == *&res_state))]
    fn fn_mut(self, args: Args, res_state: Self, res: Self::Output) {}

    #[law]
    #[trusted]
    #[ensures((*&self).postcondition_once(args, res) == ((*&self).postcondition(args, res) && resolve(&self)))]
    fn fn_once(self, args: Args, res: Self::Output) {}

    #[law]
    #[trusted]
    #[ensures((*&self).hist_inv(*&res_state) == (*&self == *&res_state))]
    fn fn_hist_inv(self, res_state: Self) {}
}

extern_spec! {
    mod std {
        mod ops {
            trait FnOnce<Args> where Args: Tuple {
                // `*&self` is meant to be `self` but, due to our encoding of contracts,
                // that would require `Self: Sized`. `*&self` avoids this.
                #[requires((*&self).precondition(arg))]
                #[ensures((*&self).postcondition_once(arg, result))]
                fn call_once(self, arg: Args) -> Self::Output;
            }

            trait FnMut<Args> where Args: Tuple {
                #[requires((*self).precondition(arg))]
                #[ensures((*self).postcondition_mut(arg, ^self, result))]
                fn call_mut(&mut self, arg: Args) -> Self::Output;
            }

            trait Fn<Args> where Args: Tuple {
                #[requires((*self).precondition(arg))]
                #[ensures((*self).postcondition(arg, result))]
                fn call(&self, arg: Args) -> Self::Output;
            }
        }
    }
}

pub trait RangeInclusiveExt<Idx> {
    #[logic]
    fn start_log(self) -> Idx;

    #[logic]
    fn end_log(self) -> Idx;

    #[logic]
    fn is_empty_log(self) -> bool
    where
        Idx: DeepModel,
        Idx::DeepModelTy: OrdLogic;
}

impl<Idx> RangeInclusiveExt<Idx> for RangeInclusive<Idx> {
    #[logic]
    #[trusted]
    fn start_log(self) -> Idx {
        dead
    }

    #[logic]
    #[trusted]
    fn end_log(self) -> Idx {
        dead
    }

    #[logic]
    #[trusted]
    #[ensures(!result ==> self.start_log().deep_model() <= self.end_log().deep_model())]
    fn is_empty_log(self) -> bool
    where
        Idx: DeepModel,
        Idx::DeepModelTy: OrdLogic,
    {
        dead
    }
}

extern_spec! {
    mod std {
        mod ops {
            impl<Idx> RangeInclusive<Idx> {
                #[ensures(result.start_log() == start)]
                #[ensures(result.end_log() == end)]
                #[ensures(start.deep_model() <= end.deep_model() ==> !result.is_empty_log())]
                fn new(start: Idx, end: Idx) -> Self
                    where Idx: DeepModel, Idx::DeepModelTy: OrdLogic;

                #[ensures(*result == self.start_log())]
                fn start(&self) -> &Idx;

                #[ensures(*result == self.end_log())]
                fn end(&self) -> &Idx;
            }

            impl<Idx: PartialOrd<Idx> + DeepModel> RangeInclusive<Idx>
            where Idx::DeepModelTy: OrdLogic
            {
                #[ensures(result == self.is_empty_log())]
                fn is_empty(&self) -> bool;
            }
        }
    }
}

extern_spec! {
    mod core {
        mod option {
            impl<T> Try for Option<T> {
                #[ensures(result == Some(output))]
                fn from_output(output: T) -> Self {
                    Some(output)
                }

                #[ensures(match self {
                    Some(v) => result == ControlFlow::Continue(v),
                    None => result == ControlFlow::Break(None)
                })]
                fn branch(self) -> ControlFlow<Option<Infallible>, T> {
                    match self {
                        Some(v) => ControlFlow::Continue(v),
                        None => ControlFlow::Break(None),
                    }
                }
            }

            impl<T> FromResidual<Option<Infallible>> for Option<T> {
                #[ensures(result == None)]
                fn from_residual(residual: Option<Infallible>) -> Self {
                    match residual {
                        None => None,
                    }
                }
            }
        }
    }
    mod core {
        mod result {
            impl<T, E> Try for Result<T, E> {
                #[ensures(result == Ok(output))]
                fn from_output(output: T) -> Self {
                    Ok(output)
                }

                #[ensures(match self {
                    Ok(v) => result == ControlFlow::Continue(v),
                    Err(e) => result == ControlFlow::Break(Err(e))
                })]
                fn branch(self) -> ControlFlow<Result<Infallible, E>, T> {
                    match self {
                        Ok(v) => ControlFlow::Continue(v),
                        Err(e) => ControlFlow::Break(Err(e)),
                    }
                }
            }

            impl<T, E, F: From<E>> FromResidual<Result<Infallible, E>> for Result<T, F> {
                #[ensures(match (result, residual) {
                   (Err(result), Err(residual)) => F::from.postcondition((residual,), result),
                    _ => false,
                })]
                fn from_residual(residual: Result<Infallible, E>) -> Self {
                    match residual {
                        Err(e) => Err(::std::convert::From::from(e)),
                    }
                }
            }
        }
    }
}

/// Dummy impls that don't use the unstable traits Tuple, FnOnce<Args>, FnMut<Args>, Fn<Args>
#[cfg(not(feature = "nightly"))]
mod impls {
    use super::*;

    impl<O, F: FnOnce() -> O> FnOnceExt<()> for F {
        type Output = O;
    }
    impl<O, F: FnMut() -> O> FnMutExt<()> for F {}
    impl<O, F: Fn() -> O> FnExt<()> for F {}

    macro_rules! impl_fn {
        ( $( $tuple:tt ),+ ) => {
            impl<$($tuple),+, O, F: FnOnce($($tuple),+) -> O> FnOnceExt<($($tuple),+,)> for F {
                type Output = O;
            }
            impl<$($tuple),+, O, F: FnMut($($tuple),+) -> O> FnMutExt<($($tuple),+,)> for F {}
            impl<$($tuple),+, O, F: Fn($($tuple),+) -> O> FnExt<($($tuple),+,)> for F {}
        };
    }

    impl_fn! { A1 }
    impl_fn! { A1, A2 }
    impl_fn! { A1, A2, A3 }
    impl_fn! { A1, A2, A3, A4 }
    impl_fn! { A1, A2, A3, A4, A5 }
    impl_fn! { A1, A2, A3, A4, A5, A6 }
    impl_fn! { A1, A2, A3, A4, A5, A6, A7 }
    impl_fn! { A1, A2, A3, A4, A5, A6, A7, A8 }
    impl_fn! { A1, A2, A3, A4, A5, A6, A7, A8, A9 }
}
