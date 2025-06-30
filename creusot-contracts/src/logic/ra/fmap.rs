use crate::{
    logic::{
        FMap,
        ra::{RA, UnitRA},
    },
    *,
};

impl<K, V: RA> RA for FMap<K, V> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        pearlite! {
            if (forall<k: K> self.get(k).op(other.get(k)) != None) {
                Some(self.total_op(other))
            } else {
                None
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        pearlite! {
            if (forall<k: K> factor.get(k).incl(self.get(k))) {
                let res = self.filter_map(|(k, vo): (K, V)|
                    match Some(vo).factor(factor.get(k)) {
                        Some(r) => r,
                        None => None,
                });
                proof_assert!(
                    match factor.op(res) {
                        None => false,
                        Some(o) => o.ext_eq(self)
                    }
                );
                Some(res)
            } else {
                None
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        pearlite! {
            forall<k: K> self.get(k).idemp()
        }
    }

    #[law]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {
        match (a.op(b), b.op(c)) {
            (Some(ab), Some(bc)) => match (ab.op(c), a.op(bc)) {
                (Some(x), Some(y)) => proof_assert!(x.ext_eq(y)),
                _ => (),
            },
            _ => (),
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(b) => b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b),
        None => forall<b: Self> ! (b.incl(self) && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        Some(self.filter_map(|(_, v): (K, V)| v.maximal_idemp()))
    }
}

impl<K, V: RA> UnitRA for FMap<K, V> {
    #[logic]
    #[open]
    #[ensures(forall<x: Self> x.op(result) == Some(x))]
    fn unit() -> Self {
        Self::empty()
    }
}

impl<K, V: RA> FMap<K, V> {
    #[logic]
    #[requires(forall<k: K> self.get(k).op(other.get(k)) != None)]
    #[ensures(forall<k: K> Some(result.get(k)) == self.get(k).op(other.get(k)))]
    pub fn total_op(self, other: Self) -> Self {
        self.merge(other, |(x, y): (V, V)| match x.op(y) {
            Some(r) => r,
            _ => such_that(|_| true),
        })
    }
}
