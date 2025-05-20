use crate::{
    logic::{FMap, ra::RA},
    *,
};

impl<K, V> RA for FMap<K, V>
where
    V: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        self.merge(other, |(x, y): (V, V)| x.op(y))
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        pearlite! {
            forall<k: K> self.get(k).valid()
        }
    }

    #[logic]
    #[open]
    #[ensures(result == exists<c: Self> self.op(c) == other)]
    #[trusted] // TODO
    fn incl(self, other: Self) -> bool {
        pearlite! {
            forall<k: K> self.get(k).incl(other.get(k))
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        pearlite! {
            forall<k: K> self.get(k).idemp()
        }
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    #[trusted] // TODO
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <V as RA>::valid_op;
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    #[trusted] // TODO
    fn maximal_idemp(self) {
        let _ = <V as RA>::maximal_idemp;
    }
}
