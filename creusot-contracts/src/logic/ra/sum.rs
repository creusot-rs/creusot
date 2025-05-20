use crate::{logic::ra::RA, *};

pub enum Sum<T, U> {
    Left(T),
    Right(U),
    SumBot,
}

#[allow(unused_imports)]
use Sum::*;

impl<T, U> RA for Sum<T, U>
where
    T: RA,
    U: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (Left(x), Left(y)) => Left(x.op(y)),
            (Right(x), Right(y)) => Right(x.op(y)),
            (_, _) => SumBot,
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Left(x) => x.valid(),
            Right(x) => x.valid(),
            SumBot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        match (self, other) {
            (Left(x), Left(y)) => x.incl(y),
            (Right(x), Right(y)) => x.incl(y),
            (_, SumBot) => true,
            (_, _) => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        match self {
            Left(x) => x.idemp(),
            Right(x) => x.idemp(),
            SumBot => true,
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
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {
        match self {
            Left(x) => x.maximal_idemp(),
            Right(x) => x.maximal_idemp(),
            SumBot => (),
        }
    }
}
