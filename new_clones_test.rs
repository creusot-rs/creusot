#![feature(unboxed_closures, tuple_trait)]

extern crate creusot_contracts;
use ::std::marker::Tuple;
pub use ::std::ops::*;
use creusot_contracts::{ensures, law, predicate, requires, trusted, Resolve};

// pub trait FnOnceExt<Args: Tuple>: FnOnce<Args> {
//     #[predicate]
//     fn precondition(self, a: Args) -> bool;

//     #[predicate]
//     fn postcondition_once(self, a: Args, res: Self::Output) -> bool;
// }

// pub trait FnMutExt<Args: Tuple>: FnMut<Args> + FnOnceExt<Args> {
//     #[predicate]
//     fn postcondition_mut(&mut self, _: Args, _: Self::Output) -> bool;

//     #[predicate]
//     fn unnest(self, _: Self) -> bool;

//     #[law]
//     #[requires(self.postcondition_mut(args, res))]
//     #[ensures((*self).unnest(^self))]
//     fn postcondition_mut_unnest(&mut self, args: Args, res: Self::Output);

//     #[law]
//     #[ensures(self.unnest(self))]
//     fn unnest_refl(self);

//     #[law]
//     #[requires(self.unnest(b))]
//     #[requires(b.unnest(c))]
//     #[ensures(self.unnest(c))]
//     fn unnest_trans(self, b: Self, c: Self);

//     #[law]
//     #[ensures(self.postcondition_once(args, res) == exists<s: &mut Self> *s == self && s.postcondition_mut(args, res) && (^s).resolve())]
//     fn fn_mut_once(self, args: Args, res: Self::Output)
//     where
//         Self: Sized;
// }

// impl<Args: Tuple, F: FnOnce<Args>> FnOnceExt<Args> for F {
//     #[predicate]
//     #[trusted]
//     fn precondition(self, _: Args) -> bool {
//         absurd
//     }

//     #[predicate]
//     #[trusted]
//     fn postcondition_once(self, _: Args, _: Self::Output) -> bool {
//         absurd
//     }
// }

// impl<Args: Tuple, F: FnMut<Args>> FnMutExt<Args> for F {
//     #[predicate]
//     #[trusted]
//     fn postcondition_mut(&mut self, _: Args, _: Self::Output) -> bool {
//         absurd
//     }

//     #[predicate]
//     #[trusted]
//     fn unnest(self, _: Self) -> bool {
//         absurd
//     }

//     #[law]
//     #[requires(self.postcondition_mut(args, res))]
//     #[ensures((*self).unnest(^self))]
//     fn postcondition_mut_unnest(&mut self, args: Args, res: Self::Output) {}

//     #[law]
//     #[ensures(self.unnest(self))]
//     fn unnest_refl(self) {}

//     #[law]
//     #[requires(self.unnest(b))]
//     #[requires(b.unnest(c))]
//     #[ensures(self.unnest(c))]
//     fn unnest_trans(self, b: Self, c: Self) {}

//     #[law]
//     #[trusted]
//     #[ensures(self.postcondition_once(args, res) == exists<s: &mut Self> *s == self && s.postcondition_mut(args, res) && (^s).resolve())]
//     fn fn_mut_once(self, args: Args, res: Self::Output) {}
// }
