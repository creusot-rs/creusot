use crate::logic::ra::{update::Update, *};

impl<T: RA> RA for Option<T> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        match (self, other) {
            (None, _) => Some(other),
            (_, None) => Some(self),
            (Some(x), Some(y)) => x.op(y).map_logic(|z| Some(z)),
        }
    }

    #[logic]
    #[open]
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

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        match self {
            None => true,
            Some(x) => x.idemp(),
        }
    }

    #[logic]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {
        let _ = <T as RA>::commutative;
    }

    #[law]
    #[open(self)]
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

    #[logic]
    #[open(self)]
    #[ensures(match result {
        Some(b) => b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b),
        None => forall<b: Self> ! (b.incl(self) && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        pearlite! {
            match self {
                None => Some(None),
                Some(x) => {
                    match x.maximal_idemp() {
                        None => Some(None),
                        Some(y) => Some(Some(y)),
                    }
                }
            }
        }
    }
}

impl<T: RA> UnitRA for Option<T> {
    #[logic]
    #[open]
    #[ensures(forall<x: Self> x.op(result) == Some(x))]
    fn unit() -> Self {
        None
    }
}

pub struct OptionUpdate<U>(pub U);

impl<R: RA, U: Update<R>> Update<Option<R>> for OptionUpdate<U> {
    type Choice = U::Choice;

    #[logic]
    #[open]
    fn premise(self, from: Option<R>) -> bool {
        match from {
            Some(from) => self.0.premise(from),
            None => false,
        }
    }

    #[logic]
    #[open]
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
