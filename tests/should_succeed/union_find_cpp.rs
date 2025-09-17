// TACTIC +compute_in_goal
extern crate creusot_contracts;

// This proof is largely adapted from the one in Vocal (see https://github.com/ocaml-gospel/vocal/blob/main/proofs/why3/UnionFind_impl.mlw)
mod implementation {
    #[cfg(creusot)]
    use creusot_contracts::logic::such_that;
    use creusot_contracts::{
        ghost::PtrOwn,
        logic::{FMap, FSet, Mapping},
        peano::PeanoInt,
        *,
    };

    pub struct Elem<T>(*const Node<T>);

    impl<T> PartialEq for Elem<T> {
        #[ensures(result == (self.deep_model() == other.deep_model()))]
        fn eq(&self, other: &Self) -> bool {
            std::ptr::addr_eq(self.0, other.0)
        }
    }
    impl<T> DeepModel for Elem<T> {
        type DeepModelTy = usize;
        #[logic]
        fn deep_model(self) -> usize {
            self.0.addr_logic()
        }
    }

    enum Node<T> {
        Root { rank: PeanoInt, payload: T },
        Link(Elem<T>),
    }

    impl<T> Clone for Elem<T> {
        #[ensures(*self == result)]
        #[check(ghost)]
        fn clone(&self) -> Self {
            Self(self.0)
        }
    }
    impl<T> Copy for Elem<T> {}

    /// Handle to the union-find data structure.
    ///
    /// This is a purely logical construct, that must be used so Creusot knows how to interpret
    /// the payloads of [`Elem`]s. It is defined as a wrapper of the `UFInner` struct below.
    /// The difference is that the wrapper has an invariant, while the inner struct does not.
    pub struct UF<T>(UFInner<T>);

    struct UFInner<T> {
        /// which "pointers" are involved
        domain: Snapshot<FSet<Elem<T>>>,
        /// Maps an element to its logical content (represented by the permission to access it).
        perms: FMap<Elem<T>, PtrOwn<Node<T>>>,
        /// Map each element in [`Self::domain`] to its payload.
        payloads: Snapshot<Mapping<Elem<T>, T>>,
        /// Map each element in [`Self::domain`] to its canonical representative.
        roots: Snapshot<Mapping<Elem<T>, Elem<T>>>,
    }

    impl<T> Invariant for UF<T> {
        #[logic]
        #[creusot::why3_attr = "inline:trivial"]
        fn invariant(self) -> bool {
            pearlite! {
            forall<e> self.0.domain.contains(e) ==>
                self.0.perms.contains(e) &&
                self.0.perms[e].ptr() == e.0 &&
                self.0.domain.contains(self.0.roots[e]) &&
                self.0.roots[self.0.roots[e]] == self.0.roots[e] &&
                match *self.0.perms[e].val() {
                    Node::Link(e2) =>
                        self.0.domain.contains(e2) &&
                        self.0.roots[e] != e &&
                        self.0.roots[e] == self.0.roots[e2],
                    Node::Root { payload, .. } =>
                        self.0.roots[e] == e &&
                        self.0.payloads[e] == payload,
                }
            }
        }
    }

    impl<T> UF<T> {
        /// Returns all the element that are handled by this union-find structure.
        #[logic]
        //#[requires(inv(self))]
        //#[ensures(forall<e1: Elem<T>, e2: Elem<T>> result.contains(e1) && result.contains(e2) && e1.deep_model() == e2.deep_model() ==> e1 == e2)]
        pub fn domain(self) -> FSet<Elem<T>> {
            *self.0.domain
        }

        /// Returns all the element that are handled by this union-find structure.
        #[logic(open)]
        pub fn in_domain(self, e: Elem<T>) -> bool {
            self.domain().contains(e)
        }

        /// Returns the map of roots of the union find.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e: Elem<T>> self.in_domain(e) ==>
            self.in_domain(result[e]) &&
            result[e] == result[result[e]]
        )]
        pub fn roots_map(self) -> Mapping<Elem<T>, Elem<T>> {
            *self.0.roots
        }

        /// Returns the root of an element. Thin wrapper around `roots_map`.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic(open)]
        pub fn root(self, e: Elem<T>) -> Elem<T> {
            self.roots_map()[e]
        }

        /// Returns the payloads associated with each element.
        #[logic]
        pub fn payloads_map(self) -> Mapping<Elem<T>, T> {
            *self.0.payloads
        }

        /// Returns the payload of an element. Thin wrapper around `payloads`.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic(open)]
        pub fn payload(self, e: Elem<T>) -> T {
            self.payloads_map()[e]
        }

        /// The internals of the union-find may have changed, but the visible state has not.
        #[logic(open, prophetic)]
        pub fn unchanged(&mut self) -> bool {
            pearlite! {
                (*self).domain() == (^self).domain() &&
                (*self).roots_map() == (^self).roots_map() &&
                (*self).payloads_map() == (^self).payloads_map()
            }
        }

        /// The set of elements have not changed.
        #[logic(open, prophetic)]
        pub fn domain_unchanged(&mut self) -> bool {
            pearlite! { (*self).domain() == (^self).domain() }
        }

        /// The payloads have not changed.
        #[logic(open, prophetic)]
        pub fn payloads_unchanged(&mut self) -> bool {
            pearlite! { (*self).payloads_map() == (^self).payloads_map() }
        }
    }

    #[ensures(result.domain().is_empty())]
    pub fn new<T>() -> Ghost<UF<T>> {
        ghost! {
            UF (
                UFInner {
                    domain: snapshot!(FSet::empty()),
                    perms: FMap::new().into_inner(),
                    payloads: snapshot!(such_that(|_| true)),
                    roots: snapshot!(such_that(|_| true)),
                }
            )
        }
    }

    #[ensures(!uf.in_domain(result))]
    #[ensures((^uf).domain() == uf.domain().insert(result))]
    #[ensures((^uf).roots_map() == uf.roots_map().set(result, result))]
    #[ensures((^uf).payloads_map() == uf.payloads_map().set(result, payload))]
    pub fn make<T>(mut uf: Ghost<&mut UF<T>>, payload: T) -> Elem<T> {
        let payload_snap = snapshot!(payload);
        let (ptr, perm) = PtrOwn::new(Node::Root { rank: PeanoInt::new(), payload });
        let elt = Elem(ptr);
        ghost! {
            let (mut perm, uf) = (perm.into_inner(), uf.into_inner());

            match uf.0.perms.get_ghost(&elt) {
                None => {},
                Some(other_perm) => PtrOwn::disjoint_lemma(&mut perm, other_perm),
            }

            uf.0.perms.insert_ghost(elt, perm);
            uf.0.domain = snapshot!(uf.0.domain.insert(elt));
            uf.0.payloads = snapshot!(uf.0.payloads.set(elt, *payload_snap));
            uf.0.roots = snapshot!(uf.0.roots.set(elt, elt));
        };
        elt
    }

    /// Find the representative element of `elem`.
    #[requires(uf.in_domain(elem))]
    #[ensures(result == uf.root(elem))]
    #[ensures(uf.unchanged())]
    pub fn find<T>(mut uf: Ghost<&mut UF<T>>, elem: Elem<T>) -> Elem<T> {
        ghost_let!(perm = uf.0.perms.get_ghost(&elem).unwrap());
        match unsafe { PtrOwn::as_ref(elem.0, perm) } {
            Node::Root { .. } => elem,
            &Node::Link(e) => {
                let root = find(ghost! {&mut **uf}, e);
                // path compression
                ghost_let!(mut uf = &mut uf.0);
                ghost_let!(mut_perm = uf.perms.get_mut_ghost(&elem).unwrap());
                unsafe { *PtrOwn::as_mut(elem.0, mut_perm) = Node::Link(root) };
                root
            }
        }
    }

    /// Get the payload of `elem`, provided it is a root.
    ///
    /// To guarantee that `elem` is a root, call [`Self::find`] before.
    #[requires(uf.in_domain(elem))]
    #[requires(uf.root(elem) == elem)]
    #[ensures(*result == uf.payload(elem))]
    pub fn get<T>(uf: Ghost<&UF<T>>, elem: Elem<T>) -> &T {
        let perm = ghost!(uf.0.perms.get_ghost(&elem).unwrap());
        match unsafe { PtrOwn::as_ref(elem.0, perm) } {
            Node::Root { payload, .. } => payload,
            _ => unreachable!(),
        }
    }

    /// If `x` and `y` are two roots, try to link them together.
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[requires(uf.root(x) == x && uf.root(y) == y)]
    #[ensures(uf.domain_unchanged() && uf.payloads_unchanged())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(result == (^uf).root(result))]
    #[ensures(forall<z> uf.in_domain(z) ==>
        (^uf).root(z) ==
            if uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y) { result } else { uf.root(z) }
    )]
    fn link<T>(mut uf: Ghost<&mut UF<T>>, x: Elem<T>, y: Elem<T>) -> Elem<T> {
        ghost_let!(mut uf = &mut uf.0);
        if x == y {
            ghost! {
                if snapshot!(x != y).into_ghost().into_inner() {
                    let (perm_x, m) = uf.perms.split_mut_ghost(&x);
                    let perm_y = m.get_mut_ghost(&y).unwrap();
                    PtrOwn::disjoint_lemma(perm_x, perm_y);
                    unreachable!()
                }
            };
            return x;
        }

        let (perm_x, mut m) = ghost!(uf.perms.split_mut_ghost(&x)).split();
        let bx = unsafe { PtrOwn::as_mut(x.0, perm_x) };
        let by = unsafe { PtrOwn::as_mut(y.0, ghost!(m.get_mut_ghost(&y).unwrap())) };

        let Node::Root { rank: rx, .. } = bx else { unreachable!() };
        let Node::Root { rank: ry, .. } = by else { unreachable!() };
        if rx < ry {
            *bx = Node::Link(y);
            ghost! { uf.roots = snapshot!(|z| { if uf.roots[z] == x { y } else { uf.roots[z] } }); };
            y
        } else {
            if rx == ry {
                rx.incr();
            }
            *by = Node::Link(x);
            ghost! { uf.roots = snapshot!(|z| { if uf.roots[z] == y { x } else { uf.roots[z] } });};
            x
        }
    }

    /// Fuse the classes of `x` and `y`.
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[ensures(uf.domain_unchanged() && uf.payloads_unchanged())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(forall<z> uf.in_domain(z) ==>
        (^uf).root(z) ==
            if uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y) { result }
            else { uf.root(z) }
    )]
    pub fn union<T>(mut uf: Ghost<&mut UF<T>>, x: Elem<T>, y: Elem<T>) -> Elem<T> {
        let rx = find(ghost! {&mut **uf}, x);
        let ry = find(ghost! {&mut **uf}, y);
        link(uf, rx, ry)
    }
}

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

    let xr = find(uf.borrow_mut(), x);
    let yr = find(uf.borrow_mut(), y);

    assert!(*get(uf.borrow(), xr) == *get(uf.borrow(), yr));
    assert!(*get(uf.borrow(), z) == 3);
}
