use crate::{logic::ra::RA, *};

/// The 'agreement' Resource Algebra.
///
/// This has the property that all resource with the same id have the same value
/// (they 'agree').
pub enum Ag<T> {
    Ag(T),
    /// The invalid value
    Bot,
}

impl<T> RA for Ag<T> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (Self::Ag(x), Self::Ag(y)) => {
                if x == y {
                    Self::Ag(x)
                } else {
                    Self::Bot
                }
            }
            (_, _) => Self::Bot,
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Self::Ag(_) => true,
            Self::Bot => false,
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
    #[ensures(match result {
        Some(c) => self.op(c) == other,
        None => forall<c: Self> self.op(c) != other,
    })]
    fn incl(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Ag(x), Self::Ag(y)) => {
                if x == y {
                    Some(Self::Ag(x))
                } else {
                    None
                }
            }
            (_, Self::Bot) => Some(Self::Bot),
            (_, Self::Ag(_)) => None,
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
    #[ensures(match result {
        Some(b) => b.incl(self) != None && b.idemp() &&
           forall<c: Self> c.incl(self) != None && c.idemp() ==> c.incl(b) != None,
        None => forall<b: Self> ! (b.incl(self) != None && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        match self {
            Self::Ag(_) => Some(self),
            Self::Bot => None,
        }
    }
}
