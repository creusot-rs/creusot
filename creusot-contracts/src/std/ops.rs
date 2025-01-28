use crate::*;
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

    #[predicate(prophetic)]
    fn precondition(self, a: Args) -> bool;

    #[predicate(prophetic)]
    fn postcondition_once(self, a: Args, res: Self::Output) -> bool;
}

/// `FnMutExt` is an extension trait for the `FnMut` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(feature = "nightly")]
pub trait FnMutExt<Args: Tuple>: FnOnceExt<Args> {
    #[predicate(prophetic)]
    fn postcondition_mut(self, _: Args, _: Self, _: Self::Output) -> bool;

    #[predicate(prophetic)]
    fn unnest(self, _: Self) -> bool;

    #[law]
    #[requires(self.postcondition_mut(args, res_state, res))]
    #[ensures(self.unnest(res_state))]
    fn postcondition_mut_unnest(self, args: Args, res_state: Self, res: Self::Output);

    #[law]
    #[ensures(self.unnest(self))]
    fn unnest_refl(self);

    #[law]
    #[requires(self.unnest(b))]
    #[requires(b.unnest(c))]
    #[ensures(self.unnest(c))]
    fn unnest_trans(self, b: Self, c: Self);

    #[law]
    #[ensures(self.postcondition_once(args, res) ==
              exists<res_state: Self> self.postcondition_mut(args, res_state, res) && resolve(&res_state))]
    fn fn_mut_once(self, args: Args, res: Self::Output)
    where
        Self: Sized;
}

/// `FnExt` is an extension trait for the `Fn` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(feature = "nightly")]
pub trait FnExt<Args: Tuple>: FnMutExt<Args> {
    #[predicate(prophetic)]
    fn postcondition(self, _: Args, _: Self::Output) -> bool;

    #[law]
    #[ensures(self.postcondition_mut(args, res_state, res) == (self == res_state && self.postcondition(args, res)))]
    fn fn_mut(self, args: Args, res_state: Self, res: Self::Output);

    #[law]
    #[ensures(self.postcondition_once(args, res) == (resolve(&self) && self.postcondition(args, res)))]
    fn fn_once(self, args: Args, res: Self::Output)
    where
        Self: Sized;
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: FnOnce<Args>> FnOnceExt<Args> for F {
    type Output = <Self as FnOnce<Args>>::Output;

    #[predicate(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_once_impl_precond"]
    fn precondition(self, args: Args) -> bool {
        true /* Dummy */
    }

    #[predicate(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_once_impl_postcond"]
    fn postcondition_once(self, args: Args, result: Self::Output) -> bool {
        true /* Dummy */
    }
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: FnMut<Args>> FnMutExt<Args> for F {
    #[predicate(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_mut_impl_postcond"]
    fn postcondition_mut(self, args: Args, result_state: Self, result: Self::Output) -> bool {
        true /* Dummy */
    }

    #[predicate(prophetic)]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_mut_impl_unnest"]
    fn unnest(self, _: Self) -> bool {
        true /* Dummy */
    }

    #[trusted]
    #[law]
    #[requires(self.postcondition_mut(args, res_state, res))]
    #[ensures(self.unnest(res_state))]
    fn postcondition_mut_unnest(self, args: Args, res_state: Self, res: Self::Output) {}

    #[trusted]
    #[law]
    #[ensures(self.unnest(self))]
    fn unnest_refl(self) {}

    #[trusted]
    #[law]
    #[requires(self.unnest(b))]
    #[requires(b.unnest(c))]
    #[ensures(self.unnest(c))]
    fn unnest_trans(self, b: Self, c: Self) {}

    #[law]
    #[trusted]
    #[ensures(self.postcondition_once(args, res) ==
              exists<res_state: Self> self.postcondition_mut(args, res_state, res) && resolve(&res_state))]
    fn fn_mut_once(self, args: Args, res: Self::Output) {}
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: Fn<Args>> FnExt<Args> for F {
    #[predicate]
    #[open]
    #[allow(unused_variables)]
    #[rustc_diagnostic_item = "fn_impl_postcond"]
    fn postcondition(self, args: Args, result: Self::Output) -> bool {
        true /* Dummy */
    }

    #[law]
    #[trusted]
    #[ensures(self.postcondition_mut(args, res_state, res) == (self == res_state && self.postcondition(args, res)))]
    fn fn_mut(self, args: Args, res_state: Self, res: Self::Output) {}

    #[law]
    #[trusted]
    #[ensures(self.postcondition_once(args, res) == (resolve(&self) && self.postcondition(args, res)))]
    fn fn_once(self, args: Args, res: Self::Output) {}
}

extern_spec! {
    mod std {
        mod ops {
            trait FnOnce<Args> where Args : Tuple {
                #[requires(self.precondition(arg))]
                #[ensures(self.postcondition_once(arg, result))]
                fn call_once(self, arg: Args) -> Self::Output;
            }

            trait FnMut<Args> where Args : Tuple {
                #[requires((*self).precondition(arg))]
                #[ensures((*self).postcondition_mut(arg, ^self, result))]
                fn call_mut(&mut self, arg: Args) -> Self::Output;
            }

            trait Fn<Args> where Args : Tuple {
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

            impl<Idx : PartialOrd<Idx> + DeepModel> RangeInclusive<Idx>
            where Idx::DeepModelTy: OrdLogic
            {
                #[ensures(result == self.is_empty_log())]
                fn is_empty(&self) -> bool;
            }
        }
    }
}

extern_spec! {
    mod std {
        mod ops {
            trait IndexMut<Idx>  where Idx : ?Sized, Self : ?Sized {
                #[requires(false)]
                fn index_mut(&mut self, ix : Idx) -> &mut Self::Output;
            }

            trait Index<Idx>  where Idx : ?Sized,  Self : ?Sized {
                #[requires(false)]
                fn index(&self, ix : Idx) -> &Self::Output;
            }
        }
    }
}

#[cfg(not(feature = "nightly"))]
pub trait FnOnceExt<Args> {
    type Output;
}

#[cfg(not(feature = "nightly"))]
pub trait FnMutExt<Args>: FnOnceExt<Args> {}

/// `FnExt` is an extension trait for the `Fn` trait, used for
/// adding a specification to closures. It should not be used directly.
#[cfg(not(feature = "nightly"))]
pub trait FnExt<Args>: FnMutExt<Args> {}

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
