use crate::{logic::ra::RA, *};

/// The 'sum' (or 'either') Resource Algebra.
///
/// This represents a resource that is in two possible states. Combining a `Left` with
/// a `Right` will yield an invalid element.
pub enum Sum<T, U> {
    Left(T),
    Right(U),
    /// The invalid value
    Bot,
}

impl<T, U> RA for Sum<T, U>
where
    T: RA,
    U: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (Self::Left(x), Self::Left(y)) => Self::Left(x.op(y)),
            (Self::Right(x), Self::Right(y)) => Self::Right(x.op(y)),
            (_, _) => Self::Bot,
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Self::Left(x) => x.valid(),
            Self::Right(x) => x.valid(),
            Self::Bot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => self.op(c) == other,
        None => forall<c: Self> self.op(c) != other,
    })]
    fn incl(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Left(x), Self::Left(y)) => match x.incl(y) {
                None => None,
                Some(z) => Some(Self::Left(z)),
            },
            (Self::Right(x), Self::Right(y)) => match x.incl(y) {
                None => None,
                Some(z) => Some(Self::Right(z)),
            },
            (_, Self::Bot) => Some(Self::Bot),
            (_, _) => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        match self {
            Self::Left(x) => x.idemp(),
            Self::Right(x) => x.idemp(),
            Self::Bot => true,
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
    fn valid_op(self, b: Self) {
        let _ = <T as RA>::valid_op;
        let _ = <U as RA>::valid_op;
    }

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
            Self::Left(x) => match x.maximal_idemp() {
                None => None,
                Some(y) => Some(Self::Left(y)),
            },
            Self::Right(x) => match x.maximal_idemp() {
                None => None,
                Some(y) => Some(Self::Right(y)),
            },
            Self::Bot => None,
        }
    }
}
