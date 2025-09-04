// TACTIC +compute_in_goal TIME 5
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
        #[check(ghost)]
        #[ensures(*result == self.deep_model())]
        fn addr(self) -> Snapshot<usize> {
            snapshot!(self.deep_model())
        }
    }

    enum Content<T> {
        Root { rank: PeanoInt, payload: T },
        Link(Element<T>),
    }

    impl<T> Clone for Element<T> {
        #[ensures(*self == result)]
        #[check(ghost)]
        fn clone(&self) -> Self {
            Self(self.0)
        }
    }
    impl<T> Copy for Element<T> {}

    type LogicAddr = Snapshot<usize>;

    /// Handle to the union-find data structure.
    ///
    /// This is a purely logical construct, that must be used so Creusot knows how to interpret
    /// the payloads of [`Element`]s. It is defined as a wrapper of the `HFInner` struct below.
    /// The difference is that the wrapper has an invariant, while the inner struct does not.
    pub struct UnionFind<T>(HFInner<T>);

    struct HFInner<T> {
        /// which "pointers" are involved
        domain: Snapshot<FSet<Element<T>>>,
        /// Maps an element to its logical content (represented by the permission to access it).
        map: FMap<LogicAddr, PtrOwn<Content<T>>>,
        /// Map each element in [`Self::domain`] to its payload.
        // `img` in the why3 proof
        payloads: Snapshot<Mapping<Element<T>, T>>,
        /// Maps each element to its distance to its root.
        distance: Snapshot<Mapping<Element<T>, Int>>,
        // `rep` in the why3 proof
        roots: Snapshot<Mapping<Element<T>, Element<T>>>,
        max_depth: Snapshot<Int>,
    }

    impl<T> Invariant for UnionFind<T> {
        #[logic]
        #[creusot::why3_attr = "inline:trivial"]
        fn invariant(self) -> bool {
            let domain = self.0.domain;
            pearlite! {
            // this invariant was not in the why3 proof: it is here because of the specifics of `DeepModel` and equality in Creusot
            (forall<e1, e2> domain.contains(e1) && domain.contains(e2) && e1.deep_model() == e2.deep_model() ==> e1 == e2) &&
            // this invariant was not in the why3 proof: it ensures that the keys and the payloads of `map` agree
            (forall<e> domain.contains(e) ==> self.0.map.contains(Snapshot::new(e.deep_model()))) &&
            (forall<e> domain.contains(e) ==> e.0 == self.get_perm(e).ptr()) &&
            (forall<e> domain.contains(e) ==> self.0.payloads[e] == self.0.payloads[self.0.roots[e]]) &&
            (forall<e> domain.contains(e) ==> self.0.roots[self.0.roots[e]] == self.0.roots[e]) &&
            (forall<e> domain.contains(e) ==> domain.contains(self.0.roots[e])) &&
            (forall<e> domain.contains(e) ==> match *self.get_perm(e).val() {
                Content::Link(e2) => e != e2 && domain.contains(e2) && self.0.roots[e] == self.0.roots[e2],
                Content::Root { rank: _, payload: v } => self.0.payloads[e] == v && self.0.roots[e] == e,
            }) &&
            (forall<e> domain.contains(e) ==> match *self.get_perm(e).val() {
                Content::Link(e2) => self.0.distance[e] < self.0.distance[e2],
                Content::Root { .. } => true,
            }) &&
            *self.0.max_depth >= 0 &&
            (forall<e> domain.contains(e) ==> 0 <= self.0.distance[e] && self.0.distance[e] <= *self.0.max_depth) &&
            (forall<e> domain.contains(e) ==> match *self.get_perm(self.0.roots[e]).val() {
                Content::Root { .. } => true,
                Content::Link { .. } => false,
            })
            }
        }
    }

    impl<T> UnionFind<T> {
        #[logic]
        fn get_perm(self, e: Element<T>) -> PtrOwn<Content<T>> {
            self.0.map[Snapshot::new(e.deep_model())]
        }

        /// Returns all the element that are handled by this union-find structure.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e1: Element<T>, e2: Element<T>> result.contains(e1) && result.contains(e2) && e1.deep_model() == e2.deep_model() ==> e1 == e2)]
        pub fn domain(self) -> FSet<Element<T>> {
            *self.0.domain
        }

        /// Returns all the element that are handled by this union-find structure.
        #[logic]
        #[open]
        pub fn in_domain(self, e: Element<T>) -> bool {
            self.domain().contains(e)
        }

        /// Returns the map of roots of the union find.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e: Element<T>> self.domain().contains(e) ==> result[e] == result[result[e]])]
        pub fn roots_map(self) -> Mapping<Element<T>, Element<T>> {
            *self.0.roots
        }

        /// Returns the root of an element. Thin wrapper around `roots_map`.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic]
        #[open]
        pub fn root(self, e: Element<T>) -> Element<T> {
            self.roots_map()[e]
        }

        /// Returns the payloads associated with each element.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e: Element<T>> self.domain().contains(e) ==> result[e] == result[self.root(e)])]
        pub fn payloads_map(self) -> Mapping<Element<T>, T> {
            *self.0.payloads
        }

        /// Returns the payload of an element. Thin wrapper around `payloads`.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic]
        #[open]
        pub fn payload(self, e: Element<T>) -> T {
            self.payloads_map()[e]
        }

        /// The internals of the union-find may have changed, but the visible state has not.
        #[logic(prophetic)]
        #[open]
        pub fn unchanged(&mut self) -> bool {
            pearlite! {
                (*self).domain() == (^self).domain() &&
                (*self).roots_map() == (^self).roots_map() &&
                (*self).payloads_map() == (^self).payloads_map()
            }
        }

        /// The set of elements have not changed.
        #[logic(prophetic)]
        #[open]
        pub fn domain_unchanged(&mut self) -> bool {
            pearlite! { (*self).domain() == (^self).domain() }
        }
    }

    #[ensures(result.domain().is_empty())]
    pub fn new<T>() -> Ghost<UnionFind<T>> {
        ghost! {
            UnionFind (
                HFInner {
                    domain: snapshot!(FSet::empty()),
                    map: FMap::new().into_inner(),
                    payloads: snapshot!(such_that(|_| true)),
                    distance: snapshot!(such_that(|_| true)),
                    roots: snapshot!(such_that(|_| true)),
                    max_depth: snapshot!(0),
                }
            )
        }
    }

    #[ensures(!uf.in_domain(result))]
    #[ensures((^uf).domain() == uf.domain().insert(result))]
    #[ensures((^uf).roots_map() == uf.roots_map().set(result, result))]
    #[ensures((^uf).payloads_map() == uf.payloads_map().set(result, payload))]
    pub fn make<T>(mut uf: Ghost<&mut UnionFind<T>>, payload: T) -> Element<T> {
        let payload_snap = snapshot!(payload);
        let (ptr, perm) = PtrOwn::new(Content::Root { rank: PeanoInt::new(), payload });
        let element = Element(ptr);
        ghost! {
            let uf = &mut uf.0;
            let perm = perm.into_inner();
            match uf.map.get_mut_ghost(&element.addr()) {
                None => {},
                Some(other_perm) => PtrOwn::disjoint_lemma(other_perm, &perm),
            }
            uf.map.insert_ghost(element.addr(), perm);
            uf.domain = snapshot!(uf.domain.insert(element));
            uf.payloads = snapshot!(uf.payloads.set(element, *payload_snap));
            uf.distance = snapshot!(uf.distance.set(element, 0));
            uf.roots = snapshot!(uf.roots.set(element, element));
        };
        element
    }

    /// Inner function, to hide specifications that only concern the distance.
    #[requires(uf.in_domain(elem))]
    #[ensures(result == uf.root(elem))]
    #[ensures(uf.unchanged())]
    // internal
    #[ensures(resolve(&mut uf.0.distance))]
    #[ensures(uf.0.distance[result] >= uf.0.distance[elem])]
    fn find_inner<T>(mut uf: Ghost<&mut UnionFind<T>>, elem: Element<T>) -> Element<T> {
        let perm = ghost!(uf.0.map.get_ghost(&elem.addr()).unwrap());
        let payload = unsafe { PtrOwn::as_ref(elem.0, perm) };
        match payload {
            Content::Root { .. } => elem,
            &Content::Link(e) => {
                let root = find_inner(ghost! {&mut **uf}, e);
                // path compression
                ghost_let!(mut map = &mut uf.0.map);
                let mut_perm = ghost!(map.get_mut_ghost(&elem.addr()).unwrap());
                unsafe { *PtrOwn::as_mut(elem.0, mut_perm) = Content::Link(root) };
                root
            }
        }
    }

    /// Find the representative element of `elem`.
    #[requires(uf.in_domain(elem))]
    #[ensures(result == uf.root(elem))]
    #[ensures(uf.unchanged())]
    pub fn find<T>(uf: Ghost<&mut UnionFind<T>>, elem: Element<T>) -> Element<T> {
        find_inner(uf, elem)
    }

    /// Get the payload of `elem`, provided it is a root.
    ///
    /// To guarantee that `elem` is a root, call [`Self::find`] before.
    #[requires(uf.in_domain(elem))]
    #[requires(uf.root(elem) == elem)]
    #[ensures(*result == uf.payload(elem))]
    pub fn get<T>(uf: Ghost<&UnionFind<T>>, elem: Element<T>) -> &T {
        let perm = ghost!(uf.0.map.get_ghost(&elem.addr()).unwrap());
        match unsafe { PtrOwn::as_ref(elem.0, perm) } {
            Content::Root { payload, .. } => payload,
            _ => loop {},
        }
    }

    /// Returns `true` if `x` and `y` are in the same class.
    #[requires(uf.in_domain(e1))]
    #[requires(uf.in_domain(e2))]
    #[ensures(result == (uf.root(e1) == uf.root(e2)))]
    #[ensures(uf.unchanged())]
    pub fn equiv<T>(mut uf: Ghost<&mut UnionFind<T>>, e1: Element<T>, e2: Element<T>) -> bool {
        let r1 = find(ghost! {&mut **uf}, e1);
        let r2 = find(uf, e2);
        std::ptr::addr_eq(r1.0, r2.0)
    }

    /// If `x` and `y` are two roots, try to link them together.
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[requires(uf.root(x) == x && uf.root(y) == y)]
    #[ensures(uf.domain_unchanged())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(result == (^uf).root(result))]
    #[ensures(forall<z> uf.in_domain(z) && (uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y)) ==>
        (^uf).root(z) == result && (^uf).payload(z) == (^uf).payload(result)
    )]
    #[ensures(forall<z> uf.in_domain(z) && uf.root(z) != uf.root(x) && uf.root(z) != uf.root(y) ==>
        (^uf).root(z) == uf.root(z) && (^uf).payload(z) == uf.payload(z)
    )]
    fn link<T>(mut uf: Ghost<&mut UnionFind<T>>, x: Element<T>, y: Element<T>) -> Element<T> {
        if x == y {
            return x;
        }
        let perm_x = ghost!(uf.0.map.get_ghost(&x.addr()).unwrap());
        let perm_y = ghost!(uf.0.map.get_ghost(&y.addr()).unwrap());
        let (rx, vx) = match unsafe { PtrOwn::as_ref(x.0, perm_x) } {
            Content::Root { rank, payload } => (rank.to_u64(), payload),
            _ => unreachable!(),
        };
        let (ry, vy) = match unsafe { PtrOwn::as_ref(y.0, perm_y) } {
            Content::Root { rank, payload } => (rank.to_u64(), payload),
            _ => unreachable!(),
        };
        if rx < ry {
            ghost_let!(mut uf = &mut uf.0);
            let perm_mut_x = ghost!(uf.map.get_mut_ghost(&x.addr()).unwrap());
            unsafe { *PtrOwn::as_mut(x.0, perm_mut_x) = Content::Link(y) };
            ghost! {
                uf.roots = snapshot!(|z| { if uf.roots[z] == x { y } else { uf.roots[z] } });
                uf.payloads = snapshot!(|z| { if uf.roots[z] == y { *vy } else { uf.payloads[z] } });
                uf.max_depth = snapshot!(*uf.max_depth + 1);
                uf.distance = snapshot!(uf.distance.set(y, 1 + uf.distance[x].max(uf.distance[y])));
            };
            y
        } else {
            ghost_let!(mut uf = &mut uf.0);
            let perm_mut_y = ghost!(uf.map.get_mut_ghost(&y.addr()).unwrap());
            unsafe { *PtrOwn::as_mut(y.0, perm_mut_y) = Content::Link(x) };
            if rx == ry {
                let perm_mut_x = ghost!(uf.map.get_mut_ghost(&x.addr()).unwrap());
                match unsafe { PtrOwn::as_mut(x.0, perm_mut_x) } {
                    Content::Root { rank, payload: _ } => *rank = rank.incr(),
                    _ => {}
                }
            }
            ghost! {
                uf.roots = snapshot!(|z| { if uf.roots[z] == y { x } else { uf.roots[z] } });
                uf.payloads = snapshot!(|z| { if uf.roots[z] == x { *vx } else { uf.payloads[z] } });
                uf.max_depth = snapshot!(*uf.max_depth + 1);
                uf.distance = snapshot!(uf.distance.set(x, 1 + uf.distance[x].max(uf.distance[y])));
            };
            x
        }
    }

    /// Link `x` and `y` together (put them in the same class).
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[ensures((^uf).domain() == uf.domain())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(forall<z> uf.in_domain(z) && (uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y)) ==>
        (^uf).root(z) == result && (^uf).payload(z) == (^uf).payload(result)
    )]
    #[ensures(forall<z> uf.in_domain(z) && uf.root(z) != uf.root(x) && uf.root(z) != uf.root(y) ==>
        (^uf).root(z) == uf.root(z) && (^uf).payload(z) == uf.payload(z)
    )]
    fn union_aux<T>(mut uf: Ghost<&mut UnionFind<T>>, x: Element<T>, y: Element<T>) -> Element<T> {
        let rx = find(ghost! {&mut **uf}, x);
        let ry = find(ghost! {&mut **uf}, y);
        link(uf, rx, ry)
    }

    /// Fuse the classes of `x` and `y`.
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[ensures((^uf).domain() == uf.domain())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(forall<z> uf.in_domain(z) && (uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y)) ==>
        (^uf).root(z) == result && (^uf).payload(z) == (^uf).payload(result)
    )]
    #[ensures(forall<z> uf.in_domain(z) && uf.root(z) != uf.root(x) && uf.root(z) != uf.root(y) ==>
        (^uf).root(z) == uf.root(z) && (^uf).payload(z) == uf.payload(z)
    )]
    pub fn union<T>(mut uf: Ghost<&mut UnionFind<T>>, x: Element<T>, y: Element<T>) -> Element<T> {
        union_aux(uf, x, y)
    }
}

use creusot_contracts::*;
use implementation::*;

pub fn example() {
    let mut uf = new::<i32>();

    let x = make(uf.borrow_mut(), 1);
    let y = make(uf.borrow_mut(), 2);
    let z = make(uf.borrow_mut(), 3);

    assert!(*get(uf.borrow(), x) == 1);
    assert!(*get(uf.borrow(), y) == 2);
    assert!(*get(uf.borrow(), z) == 3);

    union(uf.borrow_mut(), x, y);
    assert!(equiv(uf.borrow_mut(), x, y));

    let xr = find(uf.borrow_mut(), x);
    let yr = find(uf.borrow_mut(), y);

    assert!(*get(uf.borrow(), xr) == *get(uf.borrow(), yr));
    assert!(*get(uf.borrow(), z) == 3);
}

#[requires(uf.in_domain(e1) && uf.in_domain(e2))]
pub fn example_addrs_eq<T>(uf: &UnionFind<T>, e1: Element<T>, e2: Element<T>) {
    // the runtime test ensures equality of the adresses
    if e1 == e2 {
        // we get logical equality of e1 and e2 thanks to the postcondition of `domain`
        proof_assert!(e1 == e2);
    }
}
