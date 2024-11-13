use crate::*;
use ::std::marker::Tuple;
pub use ::std::ops::*;

/// `FnOnceExt` is an extension trait for the `FnOnce` trait, used for
/// adding a specification to closures. It should not be used directly.
#[rustc_diagnostic_item = "fn_once_spec"]
pub trait FnOnceExt<Args: Tuple> {
    type Output;

    #[predicate]
    fn precondition(self, a: Args) -> bool;

    #[predicate]
    fn postcondition_once(self, a: Args, res: Self::Output) -> bool;
}

/// `FnMutExt` is an extension trait for the `FnMut` trait, used for
/// adding a specification to closures. It should not be used directly.
#[rustc_diagnostic_item = "fn_mut_spec"]
pub trait FnMutExt<Args: Tuple>: FnOnceExt<Args> {
    #[predicate]
    fn postcondition_mut(&mut self, _: Args, _: Self::Output) -> bool;

    #[predicate]
    fn unnest(self, _: Self) -> bool;

    #[law]
    #[requires(self.postcondition_mut(args, res))]
    #[ensures((*self).unnest(^self))]
    fn postcondition_mut_unnest(&mut self, args: Args, res: Self::Output);

    #[law]
    #[ensures(self.unnest(self))]
    fn unnest_refl(self);

    #[law]
    #[requires(self.unnest(b))]
    #[requires(b.unnest(c))]
    #[ensures(self.unnest(c))]
    fn unnest_trans(self, b: Self, c: Self);

    #[law]
    #[ensures(self.postcondition_once(args, res) == exists<s: &mut Self> *s == self && s.postcondition_mut(args, res) && resolve(&^s))]
    fn fn_mut_once(self, args: Args, res: Self::Output)
    where
        Self: Sized;
}

/// `FnExt` is an extension trait for the `Fn` trait, used for
/// adding a specification to closures. It should not be used directly.
#[rustc_diagnostic_item = "fn_spec"]
pub trait FnExt<Args: Tuple>: FnMutExt<Args> {
    #[predicate]
    fn postcondition(&self, _: Args, _: Self::Output) -> bool;

    #[law]
    #[ensures(self.postcondition_mut(args, res) == (resolve(&self) && self.postcondition(args, res)))]
    fn fn_mut(&mut self, args: Args, res: Self::Output);

    #[law]
    #[ensures(self.postcondition_once(args, res) == (resolve(&self) && self.postcondition(args, res)))]
    fn fn_once(self, args: Args, res: Self::Output)
    where
        Self: Sized;
}

impl<Args: Tuple, F: FnOnce<Args>> FnOnceExt<Args> for F {
    type Output = <Self as FnOnce<Args>>::Output;

    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_once_impl_precond"]
    fn precondition(self, _: Args) -> bool {
        dead
    }

    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_once_impl_postcond"]
    fn postcondition_once(self, _: Args, _: Self::Output) -> bool {
        dead
    }
}

impl<Args: Tuple, F: FnMut<Args>> FnMutExt<Args> for F {
    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_mut_impl_postcond"]
    fn postcondition_mut(&mut self, _: Args, _: Self::Output) -> bool {
        dead
    }

    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_mut_impl_unnest"]
    fn unnest(self, _: Self) -> bool {
        dead
    }

    #[trusted]
    #[law]
    #[requires(self.postcondition_mut(args, res))]
    #[ensures((*self).unnest(^self))]
    fn postcondition_mut_unnest(&mut self, args: Args, res: Self::Output) {}

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
    #[ensures(self.postcondition_once(args, res) == exists<s: &mut Self> *s == self && s.postcondition_mut(args, res) && resolve(&^s))]
    fn fn_mut_once(self, args: Args, res: Self::Output) {}
}

impl<Args: Tuple, F: Fn<Args>> FnExt<Args> for F {
    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_impl_postcond"]
    fn postcondition(&self, _: Args, _: Self::Output) -> bool {
        dead
    }

    #[law]
    #[trusted]
    #[ensures(self.postcondition_mut(args, res) == (self.resolve() && self.postcondition(args, res)))]
    fn fn_mut(&mut self, args: Args, res: Self::Output) {}

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
                #[ensures(self.postcondition_mut(arg, result))]
                fn call_mut(&mut self, arg: Args) -> Self::Output;
            }

            trait Fn<Args> where Args : Tuple {
                #[requires((*self).precondition(arg))]
                #[ensures(self.postcondition(arg, result))]
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
