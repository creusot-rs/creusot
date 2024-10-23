use crate::*;
use ::std::marker::Tuple;
pub use ::std::ops::*;

/// `FnOnceExt` is an extension trait for the `FnOnce` trait, used for
/// adding a specification to closures. It should not be used directly.
#[rustc_diagnostic_item = "fn_once_spec"]
pub trait FnOnceExt<Args: Tuple>: FnOnce<Args> {
    #[predicate]
    fn precondition(self, a: Args) -> bool;

    #[predicate]
    fn postcondition_once(self, a: Args, res: Self::Output) -> bool;
}

/// `FnMutExt` is an extension trait for the `FnMut` trait, used for
/// adding a specification to closures. It should not be used directly.
#[rustc_diagnostic_item = "fn_mut_spec"]
pub trait FnMutExt<Args: Tuple>: FnMut<Args> + FnOnceExt<Args> {
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
pub trait FnExt<Args: Tuple>: Fn<Args> + FnMutExt<Args> {
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
    #[predicate]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "fn_once_impl_precond"]
    fn precondition(self, _: Args) -> bool {
        absurd
    }

    #[predicate]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "fn_once_impl_postcond"]
    fn postcondition_once(self, _: Args, _: Self::Output) -> bool {
        absurd
    }
}

impl<Args: Tuple, F: FnMut<Args>> FnMutExt<Args> for F {
    #[predicate]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "fn_mut_impl_postcond"]
    fn postcondition_mut(&mut self, _: Args, _: Self::Output) -> bool {
        absurd
    }

    #[predicate]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "fn_mut_impl_unnest"]
    fn unnest(self, _: Self) -> bool {
        absurd
    }

    #[trusted]
    #[law]
    #[open(self)]
    #[requires(self.postcondition_mut(args, res))]
    #[ensures((*self).unnest(^self))]
    fn postcondition_mut_unnest(&mut self, args: Args, res: Self::Output) {}

    #[trusted]
    #[law]
    #[open(self)]
    #[ensures(self.unnest(self))]
    fn unnest_refl(self) {}

    #[trusted]
    #[law]
    #[open(self)]
    #[requires(self.unnest(b))]
    #[requires(b.unnest(c))]
    #[ensures(self.unnest(c))]
    fn unnest_trans(self, b: Self, c: Self) {}

    #[law]
    #[trusted]
    #[open(self)]
    #[ensures(self.postcondition_once(args, res) == exists<s: &mut Self> *s == self && s.postcondition_mut(args, res) && resolve(&^s))]
    fn fn_mut_once(self, args: Args, res: Self::Output) {}
}

impl<Args: Tuple, F: Fn<Args>> FnExt<Args> for F {
    #[predicate]
    #[trusted]
    #[open(self)]
    #[rustc_diagnostic_item = "fn_impl_postcond"]
    fn postcondition(&self, _: Args, _: Self::Output) -> bool {
        absurd
    }

    #[law]
    #[open(self)]
    #[trusted]
    #[ensures(self.postcondition_mut(args, res) == (self.resolve() && self.postcondition(args, res)))]
    fn fn_mut(&mut self, args: Args, res: Self::Output) {}

    #[law]
    #[open(self)]
    #[trusted]
    #[ensures(self.postcondition_once(args, res) == (resolve(&self) && self.postcondition(args, res)))]
    fn fn_once(self, args: Args, res: Self::Output) {}
}

extern_spec! {
    mod std {
        mod ops {
            // FIXME: we should not need the `Self :` bounds, because they are implied by the main trait bound.
            // But if we remove them, some test fail.
            trait FnOnce<Args> where Self : FnOnceExt<Args>, Args : Tuple {
                #[requires(self.precondition(arg))]
                #[ensures(self.postcondition_once(arg, result))]
                fn call_once(self, arg: Args) -> Self::Output;
            }

            trait FnMut<Args> where Self : FnMutExt<Args>, Args : Tuple {
                #[requires((*self).precondition(arg))]
                #[ensures(self.postcondition_mut(arg, result))]
                fn call_mut(&mut self, arg: Args) -> Self::Output;
            }

            trait Fn<Args> where Self : FnExt<Args>, Args : Tuple {
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
    #[open(self)]
    #[logic]
    #[trusted]
    fn start_log(self) -> Idx {
        pearlite! { absurd }
    }

    #[open(self)]
    #[logic]
    #[trusted]
    fn end_log(self) -> Idx {
        pearlite! { absurd }
    }

    #[open(self)]
    #[logic]
    #[trusted]
    #[ensures(!result ==> self.start_log().deep_model() <= self.end_log().deep_model())]
    fn is_empty_log(self) -> bool
    where
        Idx: DeepModel,
        Idx::DeepModelTy: OrdLogic,
    {
        pearlite! { absurd }
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
