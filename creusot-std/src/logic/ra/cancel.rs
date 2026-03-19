#[cfg(creusot)]
use crate::logic::such_that;
use crate::{
    logic::{
        FMap, Nat,
        ra::{RA, agree::Ag, excl::Excl, sum::Sum},
        real::PositiveReal,
    },
    prelude::*,
};

/// Cancelation of resource algebra elements.
///
/// An element `e` is said to be _cancelable_ if it can be removed from a
/// composition: `∀ x y , e · x = e · y → x = y`.
pub trait Cancelable: RA {
    #[logic]
    #[ensures(result == (forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y))]
    fn cancelable(self) -> bool;
}

impl Cancelable for Int {
    #[logic]
    #[ensures(result)]
    #[ensures(forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y)]
    fn cancelable(self) -> bool {
        true
    }
}

impl Cancelable for Nat {
    #[logic]
    #[ensures(result)]
    #[ensures(forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y)]
    fn cancelable(self) -> bool {
        let _ = Nat::ext_eq;
        true
    }
}

impl Cancelable for PositiveReal {
    #[logic]
    #[ensures(result)]
    #[ensures(forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y)]
    fn cancelable(self) -> bool {
        let _ = PositiveReal::ext_eq;
        true
    }
}

impl<T: RA> Cancelable for Ag<T> {
    #[logic]
    #[ensures(result)]
    #[ensures(forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y)]
    fn cancelable(self) -> bool {
        true
    }
}

impl<T: RA> Cancelable for Excl<T> {
    #[logic]
    #[ensures(result)]
    #[ensures(forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y)]
    fn cancelable(self) -> bool {
        true
    }
}

#[logic]
fn is_exclusive<R: RA>(x: R) -> bool {
    pearlite! { forall<y> x.op(y) == None }
}

impl<L: Cancelable, R: Cancelable> Cancelable for (L, R) {
    #[logic]
    #[ensures(result == (forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y))]
    #[ensures(result ==
        (forall<l> self.0.op(l) == None) ||
        (forall<r> self.1.op(r) == None) ||
        (self.0.cancelable() && self.1.cancelable())
    )]
    fn cancelable(self) -> bool {
        pearlite! {
            if is_exclusive(self.0) || is_exclusive(self.1) {
                true
            } else {
                proof_assert!(
                    self.0.cancelable() ==>
                    (forall<x, y> self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y) ==>
                    forall<xr, yr> self.1.op(xr) != None ==> self.1.op(xr) == self.1.op(yr) ==>
                        xr == yr
                );
                if self.0.cancelable() && self.1.cancelable() {
                    true
                } else {
                    if !self.0.cancelable() {
                        let (xl, yl) = such_that(|(xl, yl): (L, L)| self.0.op(xl) != None && self.0.op(xl) == self.0.op(yl) && xl != yl);
                        let r = such_that(|r: R| self.1.op(r) != None);
                        proof_assert!(self.op((xl, r)) == self.op((yl, r)));
                    }
                    false
                }
            }
        }
    }
}

impl<T: Cancelable, U: Cancelable> Cancelable for Sum<T, U> {
    #[logic]
    #[ensures(result == (forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y))]
    #[ensures(result == (match self {
        Self::Left(l) => l.cancelable(),
        Self::Right(r) => r.cancelable(),
    }))]
    fn cancelable(self) -> bool {
        match self {
            Self::Left(l) => {
                // speeds up replay considerably
                proof_assert!(forall<x> self.op(x) != None ==> exists<lx> x == Sum::Left(lx));
                l.cancelable()
            }
            Self::Right(r) => {
                proof_assert!(forall<x> self.op(x) != None ==> exists<rx> x == Sum::Right(rx));
                r.cancelable()
            }
        }
    }
}

impl<T: Cancelable> Cancelable for Option<T> {
    #[logic]
    #[ensures(result == (forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y))]
    #[ensures(result == match self {
        None => true,
        Some(this) => this.cancelable() && this.core() == None,
    })]
    fn cancelable(self) -> bool {
        match self {
            None => true,
            Some(this) => {
                let _ = T::core_is_maximal_idemp;
                let _ = T::core_idemp;
                pearlite! {
                    if (forall<x, y> self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y) {
                        proof_assert!(self.op(this.core()) == self.op(None));
                    }
                    if this.cancelable() && this.core() == None {
                        proof_assert!(forall<x, y> self.op(x) != None ==> self.op(x) == self.op(y) ==>
                            match (x, y) {
                                (Some(x), Some(y)) => this.op(x) != None && this.op(x) == this.op(y),
                                (Some(x), None) => this.op(x) != Some(this),
                                (None, Some(y)) => this.op(y) != Some(this),
                                (None, None) => true,
                            }
                        );
                    }
                    this.cancelable() && this.core() == None
                }
            }
        }
    }
}

impl<K, V: Cancelable> Cancelable for FMap<K, V> {
    #[logic]
    #[ensures(result == (forall<x, y>
        self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y))]
    #[ensures(result == forall<k> self.get(k).cancelable())]
    fn cancelable(self) -> bool {
        pearlite! {
            if (forall<x, y> self.op(x) != None ==> self.op(x) == self.op(y) ==> x == y) {
                proof_assert!(forall<k> match self.get(k) {
                    None => true,
                    Some(v) => forall<x, y> Some(v).op(x) != None ==> Some(v).op(x) == Some(v).op(y) ==> {
                        let fx = match x {
                            None => FMap::empty(),
                            Some(x) => FMap::singleton(k, x),
                        };
                        let fy = match y {
                            None => FMap::empty(),
                            Some(y) => FMap::singleton(k, y),
                        };
                        let opx = self.op(fx).unwrap_logic();
                        let opy = self.op(fy).unwrap_logic();
                        opx.ext_eq(opy) && (opx == opy ==> fx == fy)
                    },
                });
            }
            if (forall<k> self.get(k).cancelable()) {
                proof_assert!(forall<x, y> self.op(x) != None ==> self.op(x) == self.op(y) ==> x.ext_eq(y));
            }
            forall<k> self.get(k).cancelable()
        }
    }
}
