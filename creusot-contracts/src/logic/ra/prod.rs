use crate::{
    logic::ra::{RA, UnitRA},
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

    #[predicate]
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
