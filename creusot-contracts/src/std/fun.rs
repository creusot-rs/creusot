use crate as creusot_contracts;
use creusot_contracts_proc::*;

#[rustc_diagnostic_item = "fn_once_spec"]
pub trait FnOnceSpec<Args>: FnOnce<Args> {
    #[predicate]
    fn precondition(self, a: Args) -> bool;

    #[predicate]
    fn postcondition_once(self, a: Args, res: Self::Output) -> bool;
}

#[rustc_diagnostic_item = "fn_mut_spec"]
pub trait FnMutSpec<Args>: FnMut<Args> + FnOnceSpec<Args> {
    #[predicate]
    fn postcondition_mut(&mut self, a: Args, res: Self::Output) -> bool;

    #[law]
    #[ensures((exists<s: &mut Self> *s == self && s.postcondition_mut(a, res) && (^s).resolve()) ==> self.postcondition_once(a, res))]
    #[ensures(self.postcondition_once(a, res) ==> exists<s: &mut Self> *s == self && s.postcondition_mut(a, res) && (^s).resolve())]
    fn fn_mut_once(self, a: Args, res: Self::Output)
    where
        Self: crate::Resolve + Sized;
}

#[rustc_diagnostic_item = "fn_spec"]
pub trait FnSpec<Args>: Fn<Args> + FnMutSpec<Args> {
    #[predicate]
    fn postcondition(&self, _: Args, _: Self::Output) -> bool;

    #[law]
    #[ensures(self.postcondition(args, res) ==> exists<s: &mut Self> *s == *self && s.resolve() && s.postcondition_mut(args, res))]
    #[ensures((exists<s: &mut Self> *s == *self && s.resolve() && s.postcondition_mut(args, res)) ==> self.postcondition(args, res))]
    fn fn_mut(&self, args: Args, res: Self::Output)
    where
        Self: crate::Resolve + Sized;
}

impl<Args, F: FnOnce<Args>> FnOnceSpec<Args> for F {
    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_once_impl_precond"]
    fn precondition(self, _: Args) -> bool {
        absurd
    }

    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_once_impl_postcond"]
    fn postcondition_once(self, _: Args, _: Self::Output) -> bool {
        absurd
    }
}

impl<Args, F: FnMut<Args>> FnMutSpec<Args> for F {
    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_mut_impl_postcond"]
    fn postcondition_mut(&mut self, _: Args, _: Self::Output) -> bool {
        absurd
    }

    #[law]
    fn fn_mut_once(self, _: Args, _: Self::Output) {}
}

impl<Args, F: Fn<Args>> FnSpec<Args> for F {
    #[predicate]
    #[trusted]
    #[rustc_diagnostic_item = "fn_impl_postcond"]
    fn postcondition(&self, _: Args, _: Self::Output) -> bool {
        absurd
    }

    #[law]
    fn fn_mut(&self, _: Args, _: Self::Output) {}
}

extern_spec! {
    #[requires(f.precondition(a))]
    #[ensures(f.postcondition_once(a, result))]
    fn std::ops::FnOnce::call_once<Self_, Args>(f: Self_, a: Args) -> Self_::Output
        where Self_ : FnOnceSpec<Args>
}

extern_spec! {
    #[requires((*f).precondition(a))]
    #[ensures(f.postcondition_mut(a, result))]
    fn std::ops::FnMut::call_mut<Self_, Args>(f: &mut Self_, a: Args) -> Self_::Output
        where Self_ : FnMutSpec<Args>
}

extern_spec! {
    #[requires((*f).precondition(a))]
    #[ensures(f.postcondition(a, result))]
    fn std::ops::Fn::call<Self_, Args>(f: &Self_, a: Args) -> Self_::Output
        where Self_ : FnSpec<Args>
}
