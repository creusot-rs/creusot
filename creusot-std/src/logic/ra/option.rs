#[cfg(creusot)]
use crate::logic::such_that;
use crate::{
    logic::ra::{
        RA, UnitRA,
        update::{LocalUpdate, Update},
    },
    prelude::*,
};

impl<T: RA> RA for Option<T> {
    #[logic(open)]
    fn op(self, other: Self) -> Option<Self> {
        match (self, other) {
            (None, _) => Some(other),
            (_, None) => Some(self),
            (Some(x), Some(y)) => x.op(y).map_logic(|z| Some(z)),
        }
    }

    #[logic(open)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        match (self, factor) {
            (x, None) => Some(x),
            (None, _) => None,
            (Some(x), Some(y)) => match x.factor(y) {
                Some(z) => Some(Some(z)),
                None => {
                    if x == y {
                        Some(None)
                    } else {
                        None
                    }
                }
            },
        }
    }

    #[logic(open, inline)]
    #[ensures(result == (self == other))]
    fn eq(self, other: Self) -> bool {
        match (self, other) {
            (Some(s), Some(o)) => s.eq(o),
            (None, None) => true,
            _ => false,
        }
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = <T as RA>::commutative;
    }

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        match self {
            None => Some(None),
            Some(x) => Some(x.core()),
        }
    }

    #[logic]
    #[requires(self.core() != None)]
    #[ensures({
        let c = self.core().unwrap_logic();
        c.op(c) == Some(c)
    })]
    #[ensures(self.core().unwrap_logic().op(self) == Some(self))]
    fn core_idemp(self) {
        self.core_total_idemp()
    }

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {
        match (self, i) {
            (Some(x), Some(i)) => x.core_is_maximal_idemp(i),
            _ => (),
        }
    }
}

impl<T: RA> UnitRA for Option<T> {
    #[logic(open)]
    #[ensures(forall<x: Self> #[trigger(x.op(result))] x.op(result) == Some(x))]
    fn unit() -> Self {
        None
    }

    #[logic(open)]
    #[ensures(self.core() == Some(result))]
    fn core_total(self) -> Self {
        match self {
            None => None,
            Some(x) => x.core(),
        }
    }

    #[logic]
    #[ensures(self.core_total().op(self.core_total()) == Some(self.core_total()))]
    #[ensures(self.core_total().op(self) == Some(self))]
    fn core_total_idemp(self) {
        let _ = T::core_idemp;
    }
}

/// Apply an [update](Update) to the inner value of an [`Option`] resource.
///
/// This requires the resource to be in the `Some` state.
///
/// # Example
///
/// ```
/// use creusot_std::{
///     ghost::resource::Resource,
///     logic::ra::{
///         excl::{Excl, ExclUpdate},
///         option::OptionUpdate,
///     },
///     prelude::*,
/// };
///
/// let mut res = Resource::alloc(snapshot!(Some(Excl(1))));
/// ghost! { res.update(OptionUpdate(ExclUpdate(snapshot!(2)))) };
/// proof_assert!(res@ == Some(Excl(2)));
/// ```
pub struct OptionUpdate<U>(pub U);

impl<R: RA, U: Update<R>> Update<Option<R>> for OptionUpdate<U> {
    type Choice = U::Choice;

    #[logic(open, inline)]
    fn premise(self, from: Option<R>) -> bool {
        match from {
            Some(from) => self.0.premise(from),
            None => false,
        }
    }

    #[logic(open, inline)]
    #[requires(self.premise(from))]
    fn update(self, from: Option<R>, ch: U::Choice) -> Option<R> {
        match from {
            Some(from) => Some(self.0.update(from, ch)),
            None => None, /* Dummy */
        }
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: Option<R>, frame: Option<R>) -> U::Choice {
        match frame {
            Some(frame) => self.0.frame_preserving(from.unwrap_logic(), frame),
            None => such_that(|_| true),
        }
    }
}

/// Apply an [update](LocalUpdate) to the inner value of an authority/fragment
/// pair of [`Option`]s.
///
/// This requires that both the authority and the fragment are not `None`.
pub struct OptionLocalUpdate<U>(pub U);

impl<R: RA, U: LocalUpdate<R>> LocalUpdate<Option<R>> for OptionLocalUpdate<U> {
    #[logic(open, inline)]
    fn premise(self, from_auth: Option<R>, from_frag: Option<R>) -> bool {
        match (from_auth, from_frag) {
            (Some(from_auth), Some(from_frag)) => self.0.premise(from_auth, from_frag),
            _ => false,
        }
    }

    #[logic(open, inline)]
    fn update(self, from_auth: Option<R>, from_frag: Option<R>) -> (Option<R>, Option<R>) {
        match (from_auth, from_frag) {
            (Some(from_auth), Some(from_frag)) => {
                let (to_auth, to_frag) = self.0.update(from_auth, from_frag);
                (Some(to_auth), Some(to_frag))
            }
            _ => (None, None), // Dummy
        }
    }

    #[logic]
    #[requires(self.premise(from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = self.update(from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))
    })]
    fn frame_preserving(
        self,
        from_auth: Option<R>,
        from_frag: Option<R>,
        frame: Option<Option<R>>,
    ) {
        let frame = match frame {
            None => None,
            Some(f) => f,
        };
        self.0.frame_preserving(from_auth.unwrap_logic(), from_frag.unwrap_logic(), frame)
    }
}
