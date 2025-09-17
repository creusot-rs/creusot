use crate::logic::ra::{update::Update, *};
#[cfg(creusot)]
use crate::logic::such_that;

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

    #[logic(open(self), law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = <T as RA>::commutative;
    }

    #[logic(open(self), law)]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {
        pearlite! {
            match (a, b, c) {
                (None, _, _) => {},
                (_, None, _) => {},
                (_, _, None) => {},
                (Some(aa), Some(bb), Some(cc)) => {
                    <T as RA>::associative(aa, bb, cc)
                }
            }
        }
    }

    #[logic(open)]
    #[ensures(match result {
        Some(c) => c.op(c) == Some(c) && c.op(self) == Some(self),
        None => true
    })]
    fn core(self) -> Option<Self> {
        Some(self.core_total())
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
    #[ensures(result.op(result) == Some(result))]
    #[ensures(result.op(self) == Some(self))]
    fn core_total(self) -> Self {
        match self {
            None => None,
            Some(x) => x.core(),
        }
    }

    #[logic]
    #[ensures(self.core() == Some(self.core_total()))]
    fn core_is_total(self) {}
}

pub struct OptionUpdate<U>(pub U);

impl<R: RA, U: Update<R>> Update<Option<R>> for OptionUpdate<U> {
    type Choice = U::Choice;

    #[logic(open)]
    fn premise(self, from: Option<R>) -> bool {
        match from {
            Some(from) => self.0.premise(from),
            None => false,
        }
    }

    #[logic(open)]
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
