// TACTIC +compute_in_goal
extern crate creusot_contracts;

// This proof is largely adapted from the one in Vocal (see https://github.com/ocaml-gospel/vocal/blob/main/proofs/why3/UnionFind_impl.mlw)
mod implementation {
    use creusot_contracts::{
        Clone,
        logic::{FMap, FSet, Mapping},
        peano::PeanoInt,
        ptr_own::PtrOwn,
        *,
    };

    pub struct Element<T>(*const Content<T>);

    impl<T> PartialEq for Element<T> {
        #[ensures(result == (self.deep_model() == other.deep_model()))]
        fn eq(&self, other: &Self) -> bool {
            std::ptr::addr_eq(self.0, other.0)
        }
    }
    impl<T> DeepModel for Element<T> {
        type DeepModelTy = usize;
        #[logic]
        fn deep_model(self) -> usize {
            self.0.addr_logic()
        }
    }

    impl<T> Element<T> {
        #[pure]
        #[ensures(*result == self.deep_model())]
        fn addr(self) -> Snapshot<usize> {
            snapshot!(self.deep_model())
        }
    }

    enum Content<T> {
        Root { rank: PeanoInt, value: T },
        Link(Element<T>),
    }

    impl<T> Clone for Element<T> {
        #[ensures(*self == result)]
        #[pure]
        fn clone(&self) -> Self {
            Self(self.0)
        }
    }
    impl<T> Copy for Element<T> {}

    type LogicAddr = Snapshot<usize>;

    /// Handle to the union-find data structure.
    ///
    /// This is a purely logical construct, that must be used so Creusot knows how to interpret
    /// the values of [`Element`]s.
    pub struct UnionFind<T> {
        /// which "pointers" are involved
        domain: Snapshot<FSet<Element<T>>>,
        /// Maps an element to its logical content (represented by the permission to access it).
        map: Ghost<FMap<LogicAddr, PtrOwn<Content<T>>>>,
        /// Map each element in [`Self::domain`] to its value.
        // `img` in the why3 proof
        values: Snapshot<Mapping<Element<T>, T>>,
        /// Maps each element to its distance to its root.
        distance: Snapshot<Mapping<Element<T>, Int>>,
        // `rep` in the why3 proof
        root_of: Snapshot<Mapping<Element<T>, Element<T>>>,
        max_depth: Snapshot<Int>,
    }

    impl<T> Invariant for UnionFind<T> {
        #[logic]
        #[creusot::why3_attr = "inline:trivial"]
        fn invariant(self) -> bool {
            let domain = self.domain;
            pearlite! {
            // this invariant was not in the why3 proof: it is here because of the specifics of `DeepModel` and equality in Creusot
            (forall<e1, e2> domain.contains(e1) && domain.contains(e2) && e1.deep_model() == e2.deep_model() ==> e1 == e2) &&
            // this invariant was not in the why3 proof: it ensures that the keys and the values of `map` agree
            (forall<e> domain.contains(e) ==> self.map.contains(Snapshot::new(e.deep_model()))) &&
            (forall<e> domain.contains(e) ==> e.0 == self.get_perm(e).ptr()) &&
            (forall<e> domain.contains(e) ==> self.values[e] == self.values[self.root_of[e]]) &&
            (forall<e> domain.contains(e) ==> self.root_of[self.root_of[e]] == self.root_of[e]) &&
            (forall<e> domain.contains(e) ==> domain.contains(self.root_of[e])) &&
            (forall<e> domain.contains(e) ==> match *self.get_perm(e).val() {
                Content::Link(e2) => e != e2 && domain.contains(e2) && self.root_of[e] == self.root_of[e2],
                Content::Root { rank: _, value: v } => self.values[e] == v && self.root_of[e] == e,
            }) &&
            (forall<e> domain.contains(e) ==> match *self.get_perm(e).val() {
                Content::Link(e2) => self.distance[e] < self.distance[e2],
                Content::Root { .. } => true,
            }) &&
            *self.max_depth >= 0 &&
            (forall<e> domain.contains(e) ==> 0 <= self.distance[e] && self.distance[e] <= *self.max_depth) &&
            (forall<e> domain.contains(e) ==> match *self.get_perm(self.root_of[e]).val() {
                Content::Root { .. } => true,
                Content::Link { .. } => false,
            })
            }
        }
    }

    impl<T> UnionFind<T> {
        #[ensures(result.domain.is_empty())]
        pub fn new() -> Self {
            Self {
                domain: snapshot!(FSet::empty()),
                map: FMap::new(),
                values: snapshot!(such_that(|_| true)),
                distance: snapshot!(such_that(|_| true)),
                root_of: snapshot!(such_that(|_| true)),
                max_depth: snapshot!(0),
            }
        }

        #[logic]
        fn get_perm(self, e: Element<T>) -> PtrOwn<Content<T>> {
            self.map[Snapshot::new(e.deep_model())]
        }

        /// Returns all the element that are handled by this union-find structure.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e1: Element<T>, e2: Element<T>> result.contains(e1) && result.contains(e2) && e1.deep_model() == e2.deep_model() ==> e1 == e2)]
        pub fn domain(self) -> FSet<Element<T>> {
            *self.domain
        }

        /// Returns the map of roots of the union find.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e: Element<T>> self.domain.contains(e) ==> result[e] == result[result[e]])]
        pub fn root_of(self) -> Mapping<Element<T>, Element<T>> {
            *self.root_of
        }

        /// Returns the values associated with each element.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e: Element<T>> self.domain.contains(e) ==> result[e] == result[self.root_of()[e]])]
        pub fn values(self) -> Mapping<Element<T>, T> {
            *self.values
        }

        /// The internals of the union-find may have changed, but the API did not
        #[logic(prophetic)]
        #[open]
        pub fn unchanged(&mut self) -> bool {
            pearlite! {
                (*self).domain() == (^self).domain() &&
                (*self).root_of() == (^self).root_of() &&
                (*self).values() == (^self).values()
            }
        }

        #[ensures(!(*self).domain().contains(result))]
        #[ensures((^self).domain() == (*self).domain().insert(result))]
        #[ensures((^self).root_of() == (*self).root_of().set(result, result))]
        #[ensures((^self).values() == (*self).values().set(result, value))]
        pub fn make(&mut self, value: T) -> Element<T> {
            let value_snap = snapshot!(value);
            let (ptr, perm) = PtrOwn::new(Content::Root { rank: PeanoInt::new(), value });
            let element = Element(ptr);
            ghost! {
                let perm = perm.into_inner();
                match self.map.get_mut_ghost(&element.addr()) {
                    None => {},
                    Some(other_perm) => PtrOwn::disjoint_lemma(other_perm, &perm),
                }
                self.map.insert_ghost(element.addr(), perm);
                self.domain = snapshot!(self.domain.insert(element));
                self.values = snapshot!(self.values.set(element, *value_snap));
                self.distance = snapshot!(self.distance.set(element, 0));
                self.root_of = snapshot!(self.root_of.set(element, element));
            };
            element
        }

        /// Inner function, to hide specifications that only concern the distance.
        #[requires(self.domain().contains(elem))]
        #[ensures(result == self.root_of()[elem])]
        #[ensures(self.unchanged())]
        // internal
        #[ensures((^self).distance == (*self).distance)]
        #[ensures(self.distance[result] >= self.distance[elem])]
        fn find_inner(&mut self, elem: Element<T>) -> Element<T> {
            let perm = ghost!(self.map.get_ghost(&elem.addr()).unwrap());
            let value = unsafe { PtrOwn::as_ref(elem.0, perm) };
            match value {
                Content::Root { .. } => elem,
                Content::Link(e) => {
                    let root = self.find_inner(*e);
                    // path compression
                    let mut_perm = ghost!(self.map.get_mut_ghost(&elem.addr()).unwrap());
                    unsafe { *PtrOwn::as_mut(elem.0, mut_perm) = Content::Link(root) };
                    root
                }
            }
        }

        /// Find the representative element of `elem`.
        #[requires(self.domain().contains(elem))]
        #[ensures(result == self.root_of()[elem])]
        #[ensures(self.unchanged())]
        pub fn find(&mut self, elem: Element<T>) -> Element<T> {
            self.find_inner(elem)
        }

        /// Get the value of `elem`, provided it is a root.
        ///
        /// To guarantee that `elem` is a root, call [`Self::find`] before.
        #[requires(self.domain().contains(elem))]
        #[requires(self.root_of()[elem] == elem)]
        #[ensures(*result == self.values()[elem])]
        pub fn get(&self, elem: Element<T>) -> &T {
            let perm = ghost!(self.map.get_ghost(&elem.addr()).unwrap());
            match unsafe { PtrOwn::as_ref(elem.0, perm) } {
                Content::Root { value, .. } => value,
                _ => loop {},
            }
        }

        /// Returns `true` if `x` and `y` are in the same class.
        #[requires((*self).domain().contains(e1))]
        #[requires((*self).domain().contains(e2))]
        #[ensures(result == (self.root_of()[e1] == self.root_of()[e2]))]
        #[ensures(self.unchanged())]
        pub fn equiv(&mut self, e1: Element<T>, e2: Element<T>) -> bool {
            let r1 = self.find(e1);
            let r2 = self.find(e2);
            std::ptr::addr_eq(r1.0, r2.0)
        }

        /// Returns `true` if `x` and `y` are in the same class.
        ///
        /// This is the logical version of [`Self::equiv`]
        #[logic]
        #[open]
        pub fn equiv_log(self, x: Element<T>, y: Element<T>) -> bool {
            self.root_of()[x] == self.root_of()[y]
        }

        /// If `x` and `y` are two roots, try to link them together.
        #[requires(self.domain().contains(x))]
        #[requires(self.root_of()[x] == x)]
        #[requires(self.domain().contains(y))]
        #[requires(self.root_of()[y] == y)]
        #[ensures((^self).domain() == (*self).domain())]
        #[ensures(result == (*self).root_of()[x] || result == (*self).root_of()[y])]
        #[ensures(result == (^self).root_of()[result])]
        #[ensures(forall<z: Element<T>> self.domain().contains(z) ==> (^self).root_of()[z]
            == if (*self).equiv_log(z, x) || (*self).equiv_log(z, y) {
                result
            } else {
                (*self).root_of()[z]
            }
        )]
        #[ensures(forall<z: Element<T>> self.domain().contains(z) ==> (^self).values()[z]
            == if (*self).equiv_log(z, x) || (*self).equiv_log(z, y) {
                (^self).values()[result]
            } else {
                (*self).values()[z]
            }
        )]
        fn link(&mut self, x: Element<T>, y: Element<T>) -> Element<T> {
            if x == y {
                return x;
            }
            let perm_x = ghost!(self.map.get_ghost(&x.addr()).unwrap());
            let perm_y = ghost!(self.map.get_ghost(&y.addr()).unwrap());
            let (rx, vx) = match unsafe { PtrOwn::as_ref(x.0, perm_x) } {
                Content::Root { rank, value } => (rank.to_u64(), value),
                _ => unreachable!(),
            };
            let (ry, vy) = match unsafe { PtrOwn::as_ref(y.0, perm_y) } {
                Content::Root { rank, value } => (rank.to_u64(), value),
                _ => unreachable!(),
            };
            if rx < ry {
                let perm_mut_x = ghost!(self.map.get_mut_ghost(&x.addr()).unwrap());
                unsafe { *PtrOwn::as_mut(x.0, perm_mut_x) = Content::Link(y) };
                self.root_of =
                    snapshot!(|z| { if self.root_of[z] == x { y } else { self.root_of[z] } });
                self.values =
                    snapshot!(|z| { if self.root_of[z] == y { *vy } else { self.values[z] } });
                self.max_depth = snapshot!(*self.max_depth + 1);
                self.distance =
                    snapshot!(self.distance.set(y, 1 + self.distance[x].max(self.distance[y])));
                y
            } else {
                let perm_mut_y = ghost!(self.map.get_mut_ghost(&y.addr()).unwrap());
                unsafe { *PtrOwn::as_mut(y.0, perm_mut_y) = Content::Link(x) };
                if rx == ry {
                    let perm_mut_x = ghost!(self.map.get_mut_ghost(&x.addr()).unwrap());
                    match unsafe { PtrOwn::as_mut(x.0, perm_mut_x) } {
                        Content::Root { rank, value: _ } => *rank = rank.incr(),
                        _ => {}
                    }
                }
                self.root_of =
                    snapshot!(|z| { if self.root_of[z] == y { x } else { self.root_of[z] } });
                self.values =
                    snapshot!(|z| { if self.root_of[z] == x { *vx } else { self.values[z] } });
                self.max_depth = snapshot!(*self.max_depth + 1);
                self.distance =
                    snapshot!(self.distance.set(x, 1 + self.distance[x].max(self.distance[y])));
                x
            }
        }

        /// Link `x` and `y` together (put them in the same class).
        #[requires(self.domain().contains(x))]
        #[requires(self.domain().contains(y))]
        #[ensures((^self).domain() == (*self).domain())]
        #[ensures(result == (*self).root_of()[x] || result == (*self).root_of()[y])]
        #[ensures(forall<z: Element<T>> self.domain().contains(z) ==> (^self).root_of()[z]
            == if (*self).equiv_log(z, x) || (*self).equiv_log(z, y) {
                result
            } else {
                (*self).root_of()[z]
            }
        )]
        #[ensures(forall<z: Element<T>> self.domain().contains(z) ==> (^self).values()[z]
            == if (*self).equiv_log(z, x) || (*self).equiv_log(z, y) {
                (^self).values()[result]
            } else {
                (*self).values()[z]
            }
        )]
        fn union_aux(&mut self, x: Element<T>, y: Element<T>) -> Element<T> {
            let rx = self.find(x);
            let ry = self.find(y);
            self.link(rx, ry)
        }

        /// Fuse the classes of `x` and `y`.
        #[requires(self.domain().contains(x))]
        #[requires(self.domain().contains(y))]
        #[ensures((^self).domain() == (*self).domain())]
        #[ensures(exists<r: Element<T>> (r == (*self).root_of()[x] || r == (*self).root_of()[y]) && {
            forall<z> self.domain().contains(z) ==> {
                ((^self).root_of()[z] == if (*self).equiv_log(z, x) || (*self).equiv_log(z, y) {
                    r
                } else {
                    (*self).root_of()[z]
                }) && ((^self).values()[z] == if (*self).equiv_log(z, x) || (*self).equiv_log(z, y) {
                    (^self).values()[r]
                } else {
                    (*self).values()[z]
                })
            }
        })]
        pub fn union(&mut self, x: Element<T>, y: Element<T>) {
            let _ = self.union_aux(x, y);
        }
    }
}

use creusot_contracts::*;
use implementation::{Element, UnionFind};

pub fn example() {
    let mut uf = UnionFind::<i32>::new();

    let x = uf.make(1);
    let y = uf.make(2);
    let z = uf.make(3);

    assert!(*uf.get(x) == 1);
    assert!(*uf.get(y) == 2);
    assert!(*uf.get(z) == 3);

    uf.union(x, y);
    let x = uf.find(x);
    let y = uf.find(y);

    assert!(*uf.get(x) == *uf.get(y));
    assert!(*uf.get(z) == 3);
}

#[requires(uf.domain().contains(e1) && uf.domain().contains(e2))]
pub fn example_addrs_eq<T>(uf: &UnionFind<T>, e1: Element<T>, e2: Element<T>) {
    // the runtime test ensures equality of the adresses
    if e1 == e2 {
        // we get logical equality of e1 and e2 thanks to the postcondition of `domain`
        proof_assert!(e1 == e2);
    }
}
