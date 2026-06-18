extern crate creusot_std;

// This proof is largely adapted from the one in Vocal (see https://github.com/ocaml-gospel/vocal/blob/main/proofs/why3/UnionFind_impl.mlw)
mod implementation {
    #[cfg(creusot)]
    use creusot_std::logic::any;
    use creusot_std::{
        cell::PermCell,
        ghost::perm::Perm,
        logic::{FMap, FSet, Mapping},
        peano::PeanoInt,
        prelude::*,
        std::rc::RcExt as _,
    };
    use std::rc::Rc;

    pub struct Element<T>(Rc<PermCell<Node<T>>>);

    impl<T> PartialEq for Element<T> {
        #[check(ghost)]
        #[ensures(result == (self.deep_model() == other.deep_model()))]
        #[ensures(result ==> *self == *other)]
        fn eq(&self, other: &Self) -> bool {
            Rc::ptr_eq(&self.0, &other.0)
        }
    }
    impl<T> DeepModel for Element<T> {
        type DeepModelTy = usize;
        #[logic(inline)]
        fn deep_model(self) -> usize {
            self.0.as_ptr_logic().addr_logic()
        }
    }

    enum Node<T> {
        Root { rank: PeanoInt, payload: T },
        Link(Element<T>),
    }

    impl<T> Clone for Element<T> {
        #[check(terminates)]
        #[ensures(*self == result)]
        fn clone(&self) -> Self {
            Self(self.0.clone())
        }
    }

    /// Handle to the union-find data structure.
    ///
    /// This is a purely logical construct, that must be used so Creusot knows how to interpret
    /// the payloads of [`Element`]s. It is defined as a wrapper of the `UFInner` struct below.
    /// The difference is that the wrapper has an invariant, while the inner struct does not.
    pub struct UnionFind<T>(UFInner<T>);

    struct UFInner<T> {
        /// which "pointers" are involved
        domain: Snapshot<FSet<Element<T>>>,
        /// Maps an element to its logical content (represented by the permission to access it).
        perms: FMap<Snapshot<Element<T>>, Perm<PermCell<Node<T>>>>,
        /// Map each element in [`Self::domain`] to its payload.
        // `img` in the why3 proof
        payloads: Snapshot<Mapping<Element<T>, T>>,
        // `rep` in the why3 proof
        roots: Snapshot<Mapping<Element<T>, Element<T>>>,
        /// A value which increases along pointers, for termination purposes.
        depth: Snapshot<Mapping<Element<T>, Int>>,
        max_depth: Snapshot<Int>,
    }

    impl<T> Invariant for UnionFind<T> {
        #[logic(inline)]
        fn invariant(self) -> bool {
            pearlite! { forall<e> self.0.domain.contains(e) ==>
                // This invariant was not in the why3 proof: it ensures that the keys and the payloads of `perm` agree
                self.0.perms.contains(Snapshot::new(e)) &&
                *self.0.perms[Snapshot::new(e)].ward() == *e.0.view() &&
                self.0.domain.contains(self.0.roots[e]) &&
                self.0.roots[self.0.roots[e]] == self.0.roots[e] &&
                match *self.0.perms[Snapshot::new(e)].val() {
                    Node::Link(e2) => self.0.roots[e] != e && self.0.domain.contains(e2) && self.0.roots[e] == self.0.roots[e2],
                    Node::Root { payload, .. } => self.0.roots[e] == e && self.0.payloads[e] == payload,
                } &&
                match *self.0.perms[Snapshot::new(e)].val() {
                    Node::Link(e2) => self.0.depth[e] < self.0.depth[e2],
                    Node::Root { .. } => true,
                } &&
                self.0.depth[e] <= *self.0.max_depth
            }
        }
    }

    impl<T> UnionFind<T> {
        /// Returns all the element that are handled by this union-find structure.
        #[logic]
        pub fn domain(self) -> FSet<Element<T>> {
            *self.0.domain
        }

        /// Returns all the element that are handled by this union-find structure.
        #[logic(open)]
        pub fn in_domain(self, e: Element<T>) -> bool {
            self.domain().contains(e)
        }

        /// Returns the map of roots of the union find.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<e: Element<T>> self.in_domain(e) ==>
            self.in_domain(result[e]) &&
            result[e] == result[result[e]]
        )]
        pub fn roots_map(self) -> Mapping<Element<T>, Element<T>> {
            *self.0.roots
        }

        /// Returns the root of an element. Thin wrapper around `roots_map`.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic(open)]
        pub fn root(self, e: Element<T>) -> Element<T> {
            self.roots_map()[e]
        }

        /// Returns the payloads associated with each element.
        #[logic]
        pub fn payloads_map(self) -> Mapping<Element<T>, T> {
            *self.0.payloads
        }

        /// Returns the payload of an element. Thin wrapper around `payloads`.
        ///
        /// For each element, this describes the unique root element of the associated set.
        /// The root element of a root is itself.
        #[logic(open)]
        pub fn payload(self, e: Element<T>) -> T {
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

    #[check(ghost)]
    #[ensures(result.domain().is_empty())]
    pub fn new<T>() -> Ghost<UnionFind<T>> {
        ghost! {
            UnionFind (
                UFInner {
                    domain: snapshot!(FSet::empty()),
                    perms: FMap::new().into_inner(),
                    payloads: snapshot!(any()),
                    depth: snapshot!(any()),
                    roots: snapshot!(any()),
                    max_depth: snapshot!(0),
                }
            )
        }
    }

    #[check(terminates)]
    #[ensures(!uf.in_domain(result))]
    #[ensures((^uf).domain() == uf.domain().insert(result))]
    #[ensures((^uf).roots_map() == uf.roots_map().set(result, result))]
    #[ensures((^uf).payloads_map() == uf.payloads_map().set(result, payload))]
    pub fn make<T>(mut uf: Ghost<&mut UnionFind<T>>, payload: T) -> Element<T> {
        let payload_snap = snapshot!(payload);
        let (value, perm) = PermCell::new(Node::Root { rank: PeanoInt::new(), payload });
        let elt = Element(Rc::new(value));
        ghost! {
            let (mut perm, uf) = (perm.into_inner(), uf.into_inner());

            match uf.0.perms.get_ghost(&snapshot!(elt)) {
                None => {},
                Some(other_perm) => Perm::disjoint_lemma(&mut perm, other_perm),
            }

            uf.0.perms.insert_ghost(snapshot!(elt), perm);
            uf.0.domain = snapshot!(uf.0.domain.insert(elt));
            uf.0.payloads = snapshot!(uf.0.payloads.set(elt, *payload_snap));
            uf.0.depth = snapshot!(uf.0.depth.set(elt, *uf.0.max_depth));
            uf.0.roots = snapshot!(uf.0.roots.set(elt, elt));
        };
        elt
    }

    /// Inner function, to hide specifications that only concern the depth.
    #[check(terminates)]
    #[requires(uf.in_domain(elem))]
    #[ensures(result == uf.root(elem))]
    #[ensures(uf.unchanged())]
    // internal
    #[ensures((^uf).0.depth == uf.0.depth)]
    #[ensures(uf.0.depth[result] >= uf.0.depth[elem])]
    #[variant(*uf.0.max_depth - uf.0.depth[elem])]
    fn find_inner<T>(mut uf: Ghost<&mut UnionFind<T>>, elem: Element<T>) -> Element<T> {
        let perm = ghost!(uf.0.perms.get_ghost(&snapshot!(elem)).unwrap());
        match unsafe { elem.0.borrow(perm) } {
            Node::Root { .. } => elem,
            Node::Link(e) => {
                let e = e.clone();
                let root = find_inner(ghost! {&mut **uf}, e);
                // path compression
                ghost_let!(mut uf = &mut uf.0);
                proof_assert!(uf.depth[elem] < uf.depth[root]);
                let mut_perm = ghost!(uf.perms.get_mut_ghost(&snapshot!(elem)).unwrap());
                unsafe { *elem.0.borrow_mut(mut_perm) = Node::Link(root.clone()) };
                root
            }
        }
    }

    /// Find the representative element of `elem`.
    #[check(terminates)]
    #[requires(uf.in_domain(elem))]
    #[ensures(result == uf.root(elem))]
    #[ensures(uf.unchanged())]
    pub fn find<T>(uf: Ghost<&mut UnionFind<T>>, elem: Element<T>) -> Element<T> {
        find_inner(uf, elem)
    }

    /// Get the payload of `elem`, provided it is a root.
    ///
    /// To guarantee that `elem` is a root, call [`Self::find`] before.
    #[check(terminates)]
    #[requires(uf.in_domain(*elem))]
    #[requires(uf.root(*elem) == *elem)]
    #[ensures(*result == uf.payload(*elem))]
    pub fn get<'a, T>(uf: Ghost<&'a UnionFind<T>>, elem: &'a Element<T>) -> &'a T {
        let perm = ghost!(uf.0.perms.get_ghost(&snapshot!(*elem)).unwrap());
        match unsafe { elem.0.borrow(perm) } {
            Node::Root { payload, .. } => payload,
            _ => unreachable!(),
        }
    }

    /// Returns `true` if `x` and `y` are in the same class.
    #[check(terminates)]
    #[requires(uf.in_domain(e1))]
    #[requires(uf.in_domain(e2))]
    #[ensures(result == (uf.root(e1) == uf.root(e2)))]
    #[ensures(uf.unchanged())]
    pub fn equiv<T>(mut uf: Ghost<&mut UnionFind<T>>, e1: Element<T>, e2: Element<T>) -> bool {
        let r1 = find(ghost! {&mut **uf}, e1);
        let r2 = find(uf, e2);
        r1 == r2
    }

    /// If `x` and `y` are two roots, try to link them together.
    #[check(terminates)]
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[requires(uf.root(x) == x && uf.root(y) == y)]
    #[ensures(uf.domain_unchanged() && uf.payloads_unchanged())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(result == (^uf).root(result))]
    #[ensures(forall<z> uf.in_domain(z) ==>
        (^uf).root(z) ==
            if uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y) { result } else { uf.root(z) }
    )]
    fn link<T>(mut uf: Ghost<&mut UnionFind<T>>, x: Element<T>, y: Element<T>) -> Element<T> {
        if x == y {
            return x;
        }

        ghost_let!(mut uf = &mut uf.0);

        let (perm_x, mut m) = ghost!(uf.perms.split_mut_ghost(&snapshot!(x))).split();
        let bx = unsafe { x.0.borrow_mut(perm_x) };
        let by = unsafe { y.0.borrow_mut(ghost!(m.get_mut_ghost(&snapshot!(y)).unwrap())) };

        let Node::Root { rank: rx, .. } = bx else { unreachable!() };
        let Node::Root { rank: ry, .. } = by else { unreachable!() };
        if *rx < *ry {
            *bx = Node::Link(y.clone());
            ghost! {
                uf.roots = snapshot!(|z| { if uf.roots[z] == x { y } else { uf.roots[z] } });
                uf.max_depth = snapshot!(*uf.max_depth + 1);
                uf.depth = snapshot!(uf.depth.set(y, 1 + uf.depth[x].max(uf.depth[y])));
            };
            y
        } else {
            if *rx == *ry {
                rx.incr();
            }
            *by = Node::Link(x.clone());
            ghost! {
                uf.roots = snapshot!(|z| { if uf.roots[z] == y { x } else { uf.roots[z] } });
                uf.max_depth = snapshot!(*uf.max_depth + 1);
                uf.depth = snapshot!(uf.depth.set(x, 1 + uf.depth[x].max(uf.depth[y])));
            };
            x
        }
    }

    /// Fuse the classes of `x` and `y`.
    #[check(terminates)]
    #[requires(uf.in_domain(x) && uf.in_domain(y))]
    #[ensures(uf.domain_unchanged() && uf.payloads_unchanged())]
    #[ensures(result == uf.root(x) || result == uf.root(y))]
    #[ensures(forall<z> uf.in_domain(z) ==>
        (^uf).root(z) ==
            if uf.root(z) == uf.root(x) || uf.root(z) == uf.root(y) { result }
            else { uf.root(z) }
    )]
    pub fn union<T>(mut uf: Ghost<&mut UnionFind<T>>, x: Element<T>, y: Element<T>) -> Element<T> {
        let rx = find(ghost! {&mut **uf}, x);
        let ry = find(ghost! {&mut **uf}, y);
        link(uf, rx, ry)
    }
}

use creusot_std::prelude::*;
use implementation::*;

pub fn example() {
    let mut uf = new::<i32>();

    let x = make(uf.borrow_mut(), 1);
    let y = make(uf.borrow_mut(), 2);
    let z = make(uf.borrow_mut(), 3);

    assert!(*get(uf.borrow(), &x) == 1);
    assert!(*get(uf.borrow(), &y) == 2);
    assert!(*get(uf.borrow(), &z) == 3);

    union(uf.borrow_mut(), x.clone(), y.clone());
    assert!(equiv(uf.borrow_mut(), x.clone(), y.clone()));

    let xr = find(uf.borrow_mut(), x);
    let yr = find(uf.borrow_mut(), y);

    assert!(*get(uf.borrow(), &xr) == *get(uf.borrow(), &yr));
    assert!(*get(uf.borrow(), &z) == 3);
}

#[requires(uf.in_domain(e1) && uf.in_domain(e2))]
pub fn example_addrs_eq<T>(uf: &UnionFind<T>, e1: Element<T>, e2: Element<T>) {
    // The runtime test ensures equality of the addresses
    if e1 == e2 {
        // We get logical equality of e1 and e2 thanks to the postcondition of `PartialEq`
        proof_assert!(e1 == e2);
    }
}
