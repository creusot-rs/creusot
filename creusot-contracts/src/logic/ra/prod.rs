use crate::{
    logic::ra::{
        RA, UnitRA,
        update::{LocalUpdate, Update},
    },
    *,
};

impl<T: RA, U: RA> RA for (T, U) {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        self.0.op(other.0).and_then_logic(|x| self.1.op(other.1).map_logic(|y| (x, y)))
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        match (self.0.factor(factor.0), self.1.factor(factor.1)) {
            (Some(x), Some(y)) => Some((x, y)),
            _ => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        self.0.idemp() && self.1.idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open(self)]
    #[ensures(match result {
        Some(b) => b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b),
        None => forall<b: Self> ! (b.incl(self) && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        match (self.0.maximal_idemp(), self.1.maximal_idemp()) {
            (Some(x), Some(y)) => Some((x, y)),
            _ => None,
        }
    }
}

impl<T: UnitRA, U: UnitRA> UnitRA for (T, U) {
    #[logic]
    #[ensures(forall<x: Self> x.op(result) == Some(x))]
    fn unit() -> Self {
        (T::unit(), U::unit())
    }
}

pub struct ProdUpdate<U1, U2>(pub U1, pub U2);

impl<R1: RA, R2: RA, U1: Update<R1>, U2: Update<R2>> Update<(R1, R2)> for ProdUpdate<U1, U2> {
    type Choice = (U1::Choice, U2::Choice);

    #[logic]
    #[open]
    fn premise(self, from: (R1, R2)) -> bool {
        self.0.premise(from.0) && self.1.premise(from.1)
    }

    #[logic]
    #[open]
    fn update(self, from: (R1, R2), ch: (U1::Choice, U2::Choice)) -> (R1, R2) {
        (self.0.update(from.0, ch.0), self.1.update(from.1, ch.1))
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: (R1, R2), frame: (R1, R2)) -> Self::Choice {
        (self.0.frame_preserving(from.0, frame.0), self.1.frame_preserving(from.1, frame.1))
    }
}

pub struct ProdLocalUpdate<U1, U2>(pub U1, pub U2);

impl<R1: RA, R2: RA, U1: LocalUpdate<R1>, U2: LocalUpdate<R2>> LocalUpdate<(R1, R2)>
    for ProdLocalUpdate<U1, U2>
{
    #[logic]
    #[open]
    fn premise(self, from_auth: (R1, R2), from_frag: (R1, R2)) -> bool {
        self.0.premise(from_auth.0, from_frag.0) && self.1.premise(from_auth.1, from_frag.1)
    }

    #[logic]
    #[open]
    fn update(self, from_auth: (R1, R2), from_frag: (R1, R2)) -> ((R1, R2), (R1, R2)) {
        let (to_auth0, to_frag0) = self.0.update(from_auth.0, from_frag.0);
        let (to_auth1, to_frag1) = self.1.update(from_auth.1, from_frag.1);
        ((to_auth0, to_auth1), (to_frag0, to_frag1))
    }

    #[logic]
    #[requires(LocalUpdate::premise(self, from_auth, from_frag))]
    #[requires(Some(from_frag).op(frame) == Some(Some(from_auth)))]
    #[ensures({
        let (to_auth, to_frag) = LocalUpdate::update(self, from_auth, from_frag);
        Some(to_frag).op(frame) == Some(Some(to_auth))})]
    fn frame_preserving(self, from_auth: (R1, R2), from_frag: (R1, R2), frame: Option<(R1, R2)>) {
        self.0.frame_preserving(from_auth.0, from_frag.0, frame.map_logic(|f: (R1, R2)| f.0));
        self.1.frame_preserving(from_auth.1, from_frag.1, frame.map_logic(|f: (R1, R2)| f.1));
    }
}
