use crate::{logic::ra::RA, *};

/// The 'sum' (or 'either') Resource Algebra.
///
/// This represents a resource that is in two possible states. Combining a `Left` with
/// a `Right` is invalid.
pub enum Sum<T, U> {
    Left(T),
    Right(U),
}

impl<T, U> RA for Sum<T, U>
where
    T: RA,
    U: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Self::Left(x), Self::Left(y)) => x.op(y).map_logic(|l| Self::Left(l)),
            (Self::Right(x), Self::Right(y)) => x.op(y).map_logic(|r| Self::Right(r)),
            _ => None,
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
            (Self::Left(x), Self::Left(y)) => x.factor(y).map_logic(|l| Self::Left(l)),
            (Self::Right(x), Self::Right(y)) => x.factor(y).map_logic(|r| Self::Right(r)),
            _ => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        match self {
            Self::Left(x) => x.idemp(),
            Self::Right(x) => x.idemp(),
        }
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
        match self {
            Self::Left(x) => x.maximal_idemp().map_logic(|l| Self::Left(l)),
            Self::Right(x) => x.maximal_idemp().map_logic(|r| Self::Right(r)),
        }
    }
}
