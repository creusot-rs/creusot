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

    #[logic(law)]
    #[requires(self.postcondition_mut(args, res_state, res))]
    #[ensures(self.hist_inv(res_state))]
    fn postcondition_mut_hist_inv(self, args: Args, res_state: Self, res: Self::Output);

    #[logic(law)]
    #[ensures(self.hist_inv(self))]
    fn hist_inv_refl(self);

    #[logic(law)]
    #[requires(self.hist_inv(b))]
    #[requires(b.hist_inv(c))]
    #[ensures(self.hist_inv(c))]
    fn hist_inv_trans(self, b: Self, c: Self);

    #[logic(law)]
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

    #[logic(law)]
    #[ensures(self.postcondition_mut(args, res_state, res) == (self.postcondition(args, res) && self == res_state))]
    fn fn_mut(self, args: Args, res_state: Self, res: Self::Output);

    #[logic(law)]
    #[ensures(self.postcondition_once(args, res) == (self.postcondition(args, res) && resolve(self)))]
    fn fn_once(self, args: Args, res: Self::Output);

    #[logic(law)]
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

    #[logic(open, prophetic, inline)]
    #[allow(unused_variables)]
    #[intrinsic("precondition")]
    fn precondition(self, args: Args) -> bool {
        dead
    }

    #[logic(open, prophetic, inline)]
    #[allow(unused_variables)]
    #[intrinsic("postcondition_once")]
    fn postcondition_once(self, args: Args, result: Self::Output) -> bool {
        dead
    }
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: ?Sized + FnMut<Args>> FnMutExt<Args> for F {
    #[logic(open, prophetic, inline)]
    #[allow(unused_variables)]
    #[intrinsic("postcondition_mut")]
    fn postcondition_mut(self, args: Args, result_state: Self, result: Self::Output) -> bool {
        dead
    }

    #[logic(open, prophetic, inline)]
    #[allow(unused_variables)]
    #[intrinsic("hist_inv")]
    fn hist_inv(self, result_state: Self) -> bool {
        dead
    }

    #[trusted]
    #[logic(law)]
    #[requires(self.postcondition_mut(args, res_state, res))]
    #[ensures(self.hist_inv(res_state))]
    fn postcondition_mut_hist_inv(self, args: Args, res_state: Self, res: Self::Output) {}

    #[trusted]
    #[logic(law)]
    #[ensures(self.hist_inv(self))]
    fn hist_inv_refl(self) {}

    #[trusted]
    #[logic(law)]
    #[requires(self.hist_inv(b))]
    #[requires(b.hist_inv(c))]
    #[ensures(self.hist_inv(c))]
    fn hist_inv_trans(self, b: Self, c: Self) {}

    #[logic(law)]
    #[trusted]
    #[ensures(self.postcondition_once(args, res) ==
              exists<res_state: Self> self.postcondition_mut(args, res_state, res) && resolve(res_state))]
    fn fn_mut_once(self, args: Args, res: Self::Output) {}
}

#[cfg(feature = "nightly")]
impl<Args: Tuple, F: ?Sized + Fn<Args>> FnExt<Args> for F {
    #[logic(open, inline)]
    #[allow(unused_variables)]
    #[intrinsic("postcondition")]
    fn postcondition(self, args: Args, result: Self::Output) -> bool {
        dead
    }

    #[logic(law)]
    #[trusted]
    #[ensures(self.postcondition_mut(args, res_state, res) == (self.postcondition(args, res) && self == res_state))]
    fn fn_mut(self, args: Args, res_state: Self, res: Self::Output) {}

    #[logic(law)]
    #[trusted]
    #[ensures(self.postcondition_once(args, res) == (self.postcondition(args, res) && resolve(self)))]
    fn fn_once(self, args: Args, res: Self::Output) {}

    #[logic(law)]
    #[trusted]
    #[ensures(self.hist_inv(res_state) == (self == res_state))]
    fn fn_hist_inv(self, res_state: Self) {}
}

extern_spec! {
    mod std {
        mod ops {
            trait FnOnce<Args> where Args: Tuple {
                #[requires(self.precondition(arg))]
                #[ensures(self.postcondition_once(arg, result))]
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

            trait Deref {
                #[check(ghost)]
                #[requires(false)]
                fn deref(&self) -> &Self::Target;
            }

            trait DerefMut {
                #[check(ghost)]
                #[requires(false)]
                fn deref_mut(&mut self) -> &mut Self::Target;
            }
        }
    }
}

impl<T: DeepModel> DeepModel for Bound<T> {
    type DeepModelTy = Bound<T::DeepModelTy>;

    #[logic]
    fn deep_model(self) -> Self::DeepModelTy {
        match self {
            Bound::Included(b) => Bound::Included(b.deep_model()),
            Bound::Excluded(b) => Bound::Excluded(b.deep_model()),
            Bound::Unbounded => Bound::Unbounded,
        }
    }
}

/// Methods for the specification of [`::std::ops::RangeBounds`].
pub trait RangeBounds<T: ?Sized + DeepModel<DeepModelTy: OrdLogic>>:
    ::std::ops::RangeBounds<T>
{
    #[logic]
    fn start_bound_logic(&self) -> Bound<&T>;

    #[logic]
    fn end_bound_logic(&self) -> Bound<&T>;
}

/// Membership to an interval `(Bound<T>, Bound<T>)`.
#[logic(open)]
pub fn between<T: OrdLogic>(lo: Bound<T>, item: T, hi: Bound<T>) -> bool {
    lower_bound(lo, item) && upper_bound(item, hi)
}

/// Comparison with a lower bound.
#[logic(open)]
pub fn lower_bound<T: OrdLogic>(lo: Bound<T>, item: T) -> bool {
    pearlite! {
        match lo {
            Bound::Included(lo) => lo <= item,
            Bound::Excluded(lo) => lo < item,
            Bound::Unbounded => true,
        }
    }
}

/// Comparison with an upper bound.
#[logic(open)]
pub fn upper_bound<T: OrdLogic>(item: T, hi: Bound<T>) -> bool {
    pearlite! {
        match hi {
            Bound::Included(hi) => item <= hi,
            Bound::Excluded(lo) => lo < item,
            Bound::Unbounded => true,
        }
    }
}

extern_spec! {
    mod std {
        mod ops {
            trait RangeBounds<T>
            where
                Self: RangeBounds<T>,
                T: ?Sized + DeepModel,
                T::DeepModelTy: OrdLogic,
            {
                #[ensures(result == self.start_bound_logic())]
                fn start_bound(&self) -> Bound<&T>;

                #[ensures(result == self.end_bound_logic())]
                fn end_bound(&self) -> Bound<&T>;

                #[ensures(between(self.start_bound_logic().deep_model(), item.deep_model(), self.end_bound_logic().deep_model()))]
                fn contains<U>(&self, item: &U) -> bool
                where
                    T: PartialOrd<U>,
                    U: ?Sized + PartialOrd<T> + DeepModel<DeepModelTy = T::DeepModelTy>;

                #[ensures(!exists<item: T::DeepModelTy> between(self.start_bound_logic().deep_model(), item, self.end_bound_logic().deep_model()))]
                fn is_empty(&self) -> bool
                where T: PartialOrd;
            }
        }
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeFull {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeFrom<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeTo<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for Range<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeInclusive<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start_log())
    }

    #[logic(opaque)]
    fn end_bound_logic(&self) -> Bound<&T> {
        dead
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeToInclusive<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for (Bound<T>, Bound<T>) {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        match *self {
            (Bound::Included(ref start), _) => Bound::Included(start),
            (Bound::Excluded(ref start), _) => Bound::Excluded(start),
            (Bound::Unbounded, _) => Bound::Unbounded,
        }
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        match *self {
            (_, Bound::Included(ref end)) => Bound::Included(end),
            (_, Bound::Excluded(ref end)) => Bound::Excluded(end),
            (_, Bound::Unbounded) => Bound::Unbounded,
        }
    }
}

impl<'a, T: ?Sized + 'a + DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T>
    for (Bound<&'a T>, Bound<&'a T>)
{
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        self.0
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        self.1
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeFrom<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeTo<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for Range<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

// I don't know why this impl is different from the one for `RangeInclusive<T>`.
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeInclusive<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start_log())
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.end_log())
    }
}

impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for RangeToInclusive<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.end)
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for ::std::range::Range<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(&self.end)
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for ::std::range::Range<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Excluded(self.end)
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for ::std::range::RangeFrom<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for ::std::range::RangeFrom<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Unbounded
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for ::std::range::RangeInclusive<T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(&self.last)
    }
}

#[cfg(feature = "nightly")]
impl<T: DeepModel<DeepModelTy: OrdLogic>> RangeBounds<T> for ::std::range::RangeInclusive<&T> {
    #[logic(open)]
    fn start_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.start)
    }

    #[logic(open)]
    fn end_bound_logic(&self) -> Bound<&T> {
        Bound::Included(self.last)
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
    #[logic(opaque)]
    fn start_log(self) -> Idx {
        dead
    }

    #[logic(opaque)]
    fn end_log(self) -> Idx {
        dead
    }

    #[logic(opaque)]
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
