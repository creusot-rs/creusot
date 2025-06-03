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
    #[open(self)]
    #[ensures(match result {
        Some(c) => self.op(c) == other,
        None => forall<c: Self> self.op(c) != other,
    })]
    fn incl(self, other: Self) -> Option<Self> {
        let res = pearlite! { forall<k: K> self.get(k).incl(other.get(k)) != None };
        if res {
            let missing_part = missing_part(self, other);
            proof_assert!(forall<k: K> match (other.get(k), self.get(k)) {
                (Some(vo), Some(vs)) => if vo == vs { true } else {
                    exists<v: V> vs.op(v) == vo && missing_part.get(k) == Some(v)
                }
                _ => true,
            });
            proof_assert!(self.op(missing_part).ext_eq(other));
            Some(missing_part)
        } else {
            None
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
    fn associative(a: Self, b: Self, c: Self) {
        proof_assert!(a.op(b).op(c).ext_eq(a.op(b.op(c))));
    }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <V as RA>::valid_op;
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
        let _ = <V as RA>::maximal_idemp;
        pearlite! {
            if !(forall<b: Self> ! (b.incl(self) != None && b.idemp())) {
                let included = maximal_idemp_part(self);
                proof_assert!(included.incl(self) != None && included.idemp() &&
                    forall<c: Self> c.incl(self) != None && c.idemp() ==> c.incl(included) != None);
                Some(included)
            } else {
                None
            }
        }
    }
}

/// Used in `<FMap as RA>::incl`.
#[logic]
fn missing_part<K, V: RA>(this: FMap<K, V>, other: FMap<K, V>) -> FMap<K, V> {
    other.filter_map(|(k, vo)| match this.get(k) {
        None => Some(vo),
        Some(vs) => {
            if vs == vo {
                None
            } else {
                Some(such_that(|v| vs.op(v) == vo))
            }
        }
    })
}

/// Used in `<FMap as RA>::maximal_idemp`.
#[logic]
fn maximal_idemp_part<K, V: RA>(this: FMap<K, V>) -> FMap<K, V> {
    pearlite! {
        this.filter_map(|(_, v)| if forall<v2: V> ! (v2.incl(v) != None && v2.idemp()) {
            None
        } else {
            Some(such_that(|v2: V| v2.incl(v) != None && v2.idemp() && forall<c: V> c.incl(v) != None && c.idemp() ==> c.incl(v2) != None))
        })
    }
}
