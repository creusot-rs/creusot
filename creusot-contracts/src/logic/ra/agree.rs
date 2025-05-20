use crate::{logic::ra::RA, *};

pub enum Ag<T> {
    Ag(T),
    AgBot,
}

#[allow(unused_imports)]
use Ag::*;

impl<T> RA for Ag<T> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (Ag(x), Ag(y)) => {
                if x == y {
                    Ag(x)
                } else {
                    AgBot
                }
            }
            (_, _) => AgBot,
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Ag(_) => true,
            AgBot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        true
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        match (self, other) {
            (Ag(x), Ag(y)) => x == y,
            (_, AgBot) => true,
            (_, Ag(_)) => false,
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {}

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {}
}
