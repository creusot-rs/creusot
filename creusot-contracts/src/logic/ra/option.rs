use crate::*;
use crate::logic::ra::RA;

impl<T> RA for Option<T>
    where T: RA
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        match (self, other) {
            (None, _) => other,
            (_, None) => self,
            (Some(x), Some(y)) => Some(x.op(y)),
        }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Some(x) => x.valid(),
            None => true,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        match (self, other) {
            (None, _) => true,
            (_, None) => false,
            (Some(x), Some(y)) => {
                x == y || x.incl(y)
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
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
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { pearlite!{
        match (a, b, c) {
            (None, _, _) => {},
            (_, None, _) => {},
            (_, _, None) => {},
            (Some(aa), Some(bb), Some(cc)) => {
                <T as RA>::associative(aa, bb, cc)
            }
        }
    }}

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <T as RA>::valid_op;
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) { pearlite!{
        match self {
            None => (),
            Some(x) => {
                x.maximal_idemp();
                if forall<y: T> ! (y.incl(x) && y.idemp()) {
                    // pick None, show the right-hand side of the postcondition
                    proof_assert!(None.incl(self) && None::<T>.idemp());
                    proof_assert!(forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(None));
                } else {
                    // pick Some(y)
                    proof_assert!(exists<y: T> y.incl(x) && y.idemp() &&
                      Some(y).incl(self) && Some(y).idemp() &&
                      (forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(Some(y)))
                    );
                }
            }
        }
    }}
}
