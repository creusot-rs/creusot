extern crate creusot_std;

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_std::{
        cell::PermCell,
        ghost::{
            invariant::{
                NonAtomicInvariant, NonAtomicInvariantExt as _, Protocol, Tokens, declare_namespace,
            },
            perm::Perm,
            resource::{Authority, Fragment},
        },
        logic::{
            FMap, Id, Mapping,
            ra::{agree::Ag, fmap::FMapInsertLocalUpdate},
        },
        prelude::*,
    };

    declare_namespace! { PARRAY }

    /// A type of persistent arrays
    ///
    /// Persistent arrays have the following properties:
    /// - they can be freely (and cheaply) cloned
    /// - they can cheaply create new modified versions, without affecting the other copies
    ///
    /// # Safety
    ///
    /// All methods marked `unsafe` are actually safe to use, _as long as you check the
    /// program with Creusot_.
    ///
    /// If you don't, you must ensure that the reference returned by
    /// [`Self::get`] is dropped before doing any other operation on any array.
    pub struct PersistentArray<T> {
        /// Contains a pointer to the actual value
        permcell: Rc<PermCell<Inner<T>>>,
        /// Fragment of the GMap resource.
        ///
        /// This contains a fragment of the map, with only `permcell` as key.
        /// The corresponding value is the logical value of the map.
        frag: Ghost<Fragment<FMap<PermCell<Inner<T>>, Ag<Seq<T>>>>>,
        /// The [`Id`] in the public part is the id of the whole `GMap`, **not** the individual keys !
        inv: Ghost<Rc<NonAtomicInvariant<PA<T>>>>,
    }

    impl<T> Clone for PersistentArray<T> {
        #[ensures(result@ == self@)]
        fn clone(&self) -> Self {
            Self {
                permcell: self.permcell.clone(),
                frag: ghost!(self.frag.core()),
                inv: ghost!(self.inv.clone()),
            }
        }
    }

    impl<T> Invariant for PersistentArray<T> {
        #[logic]
        fn invariant(self) -> bool {
            pearlite! {
                // We indeed have the corresponding fragment of the invariant
                self.frag.id() == self.inv@.public()
                && self.frag@.get(*self.permcell@) != None
                && self.inv@.namespace() == PARRAY()
            }
        }
    }

    enum Inner<T> {
        Direct(Vec<T>),
        Link { index: usize, value: T, next: Rc<PermCell<Inner<T>>> },
    }

    impl<T> View for PersistentArray<T> {
        type ViewTy = Seq<T>;
        #[logic(inline)]
        fn view(self) -> Seq<T> {
            pearlite! { self.frag@.get(*self.permcell@).unwrap_logic().0 }
        }
    }

    /// Structure describing the invariants respected by the pointers.
    struct PA<T> {
        /// Holds the permission for each pointer.
        perms: FMap<Snapshot<PermCell<Inner<T>>>, Box<Perm<PermCell<Inner<T>>>>>,
        /// Holds the 'authoritative' version of the map of logical values.
        ///
        /// When we open the invariant, we get (a mutable borrow to) this, and can learn
        /// that some persistent array is in the map with some value.
        auth: Authority<FMap<PermCell<Inner<T>>, Ag<Seq<T>>>>,
        /// Rank: used to show that there is no cycle in our structure. Useful in `reroot`.
        depth: Snapshot<Mapping<PermCell<Inner<T>>, Int>>,
    }

    impl<T> Protocol for PA<T> {
        type Public = Id;

        #[logic(inline)]
        fn protocol(self, id: Id) -> bool {
            pearlite! {
                self.partial_invariant(id) &&
                forall<pc> self.auth@.contains(pc) == self.perms.contains(Snapshot::new(pc))
            }
        }
    }

    impl<T> PA<T> {
        #[logic(inline)]
        fn partial_invariant(self, id: Id) -> bool {
            pearlite! {
                self.auth.id() == id &&
                forall<pc: Snapshot<_>> self.auth@.contains(*pc) && self.perms.contains(pc) ==>
                    *self.perms[pc].ward() == *pc &&
                    match self.perms[pc].val() {
                        Inner::Direct(v) => self.auth@[*pc].0 == v@,
                        Inner::Link { index, value, next } =>
                            // If `Link { next, .. }` is in the map, then `next` is also in the map.
                            self.auth@.contains(*next@) &&
                            // The depth decreases when following the links
                            self.depth[*pc] > self.depth[*next@] &&
                            index@ < self.auth@[*next@].0.len() &&
                            self.auth@[*pc].0 == self.auth@[*next@].0.set(index@, *value)
                    }
            }
        }
    }

    impl<T> PersistentArray<T> {
        /// Create a new array from the given vector of values
        #[ensures(result@ == v@)]
        pub fn new(v: Vec<T>) -> Self {
            let new_ag = snapshot!(Ag(v@));
            let (permcell, perm) = PermCell::new(Inner::Direct(v));
            let mut auth = Authority::alloc();
            let mut frag = ghost!(Fragment::new_unit(auth.id_ghost()));
            ghost!(auth.update(&mut frag, FMapInsertLocalUpdate(snapshot!(*perm.ward()), new_ag)));

            let inv = ghost! {
                let mut perms = FMap::new();
                perms.insert_ghost(snapshot!(*perm.ward()), perm.into_inner());
                let na_inv = NonAtomicInvariant::new(
                    ghost!(PA {
                        perms: perms.into_inner(),
                        auth: auth.into_inner(),
                        depth: snapshot!(|_| 0),
                    }),
                    snapshot!(frag.id()),
                    snapshot!(PARRAY()),
                );
                Rc::new(na_inv.into_inner())
            };

            Self { permcell: Rc::new(permcell), frag, inv }
        }

        /// Return a new array, where the value at index `index` has been set to `value`
        #[requires(index@ < self@.len())]
        #[requires(tokens.contains(PARRAY()))]
        #[ensures(result@ == self@.set(index@, value))]
        pub fn set(&self, index: usize, value: T, tokens: Ghost<Tokens>) -> Self {
            let new_ag = snapshot!(Ag(self@.set(index@, value)));
            let (permcell, perm) =
                PermCell::new(Inner::Link { index, value, next: self.permcell.clone() });
            let frag = self.inv.open(tokens, |mut pa| {
                ghost! {
                    // prove that self is contained in the map by validity
                    pa.auth.frag_lemma(&self.frag);
                    // prove that we are inserting a _new_ value
                    if let Some(other) = pa.perms.get_mut_ghost(&snapshot!(permcell)) {
                        Perm::disjoint_lemma(other, &perm);
                        proof_assert!(false)
                    }
                    pa.perms.insert_ghost(snapshot!(permcell), perm.into_inner());
                    pa.depth = snapshot!(pa.depth.set(permcell, pa.depth[*self.permcell@] + 1));
                    let mut frag = Fragment::new_unit(pa.auth.id_ghost());
                    pa.auth.update(&mut frag, FMapInsertLocalUpdate(snapshot!(permcell), new_ag));
                    frag
                }
            });
            Self { permcell: Rc::new(permcell), frag, inv: ghost!(self.inv.clone()) }
        }

        /// Get the value of the array at index `i`.
        ///
        /// If `i` is out of bounds, return `None`.
        ///
        /// # Performances
        ///
        /// If the current array has been obtained after many calls to set, this method
        /// will have to do a lot of pointer chasing to find the value.
        ///
        /// If you use this method often on the same array, consider using [`Self::get`]
        /// instead.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(tokens.contains(PARRAY()))]
        #[requires(index@ < self@.len())]
        #[ensures(*result == self@[index@])]
        pub unsafe fn get_immut<'a>(&'a self, index: usize, tokens: Ghost<&'a Tokens>) -> &'a T {
            let pa = ghost!(self.inv.open_const(*tokens));
            // prove that self is contained in the map by validity
            ghost! { pa.auth.frag_lemma(&self.frag) };
            unsafe { Self::get_inner_immut(&self.permcell, index, pa) }
        }

        #[requires(exists<p> pa.protocol(p))]
        #[requires(pa.auth@.contains(*inner@))]
        #[requires(i@ < pa.auth@[*inner@].0.len())]
        #[ensures(*result == pa.auth@[*inner@].0[i@])]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PermCell<Inner<T>>>,
            i: usize,
            pa: Ghost<&'a PA<T>>,
        ) -> &'a T {
            match unsafe { inner.borrow(ghost!(pa.perms.get_ghost(&snapshot!(*inner@)).unwrap())) }
            {
                Inner::Direct(v) => &v[i],
                Inner::Link { index, value, .. } if i == *index => value,
                Inner::Link { next, .. } => unsafe { Self::get_inner_immut(next, i, pa) },
            }
        }

        /// Get the value of the array at index `i`.
        ///
        /// If `i` is out of bounds, return `None`.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(tokens.contains(PARRAY()))]
        #[requires(index@ < self@.len())]
        #[ensures(*result == self@[index@])]
        pub unsafe fn get<'a>(&'a self, index: usize, tokens: Ghost<Tokens<'a>>) -> &'a T {
            let auth_id = snapshot!(self.inv@.public());
            self.inv.open(tokens, |mut pa| {
                // prove that self is contained in the map by validity
                ghost! { pa.auth.frag_lemma(&self.frag) };
                Self::reroot(&self.permcell, auth_id, ghost!(&mut *pa));
                let perm = ghost!(
                    &**pa.into_inner().perms.get_ghost(&snapshot!(*self.permcell@)).unwrap()
                );
                let Inner::Direct(arr) = (unsafe { self.permcell.borrow(perm) }) else {
                    unreachable!()
                };
                unsafe { arr.get_unchecked(index) }
            })
        }

        /// Reroot the array: at the end of this function, `inner` will point directly
        /// to the underlying array.
        #[requires(pa.partial_invariant(*auth_id))]
        #[requires(pa.auth@.contains(*cur@))]
        #[requires(forall<id> pa.auth@.contains(id) && pa.depth[id] <= pa.depth[*cur@]
            ==> pa.perms.contains(Snapshot::new(id))
        )]
        #[ensures((^pa).partial_invariant(*auth_id))]
        #[ensures((^pa).auth == pa.auth)]
        #[ensures(forall<id: Snapshot<_>> pa.depth[*id] > pa.depth[*cur@] ==>
            pa.perms.get(id) == (^pa).perms.get(id) && pa.depth[*id] == (^pa).depth[*id])]
        #[ensures(forall<id> (^pa).perms.contains(id) == pa.perms.contains(id))]
        #[ensures(match *(^pa).perms[Snapshot::new(*cur@)].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        fn reroot(cur: &Rc<PermCell<Inner<T>>>, auth_id: Snapshot<Id>, mut pa: Ghost<&mut PA<T>>) {
            // We take ownership of cur
            let mut perm_cur = ghost!(pa.perms.remove_ghost(&snapshot!(*cur@)).unwrap());
            let bor_cur = unsafe { cur.borrow_mut(ghost!(&mut perm_cur)) };

            // If we are already at the root, we are done
            let Inner::Link { next, value, index } = bor_cur else {
                ghost!(pa.perms.insert_ghost(snapshot!(*cur@), perm_cur.into_inner()));
                return;
            };

            // Recursively reroot the next node
            Self::reroot(&next, auth_id, ghost!(&mut *pa));

            // Change the next field
            let next = std::mem::replace(next, cur.clone());

            // Take the ownership of next
            let perm_next = ghost! { &mut **pa.perms.get_mut_ghost(&snapshot!(*next@)).unwrap() };
            let bor_next = unsafe { next.borrow_mut(perm_next) };

            // Exchange the value field witht the content of the array
            let Inner::Direct(arr) = bor_next else { unreachable!() };
            std::mem::swap(&mut arr[*index], value);

            // Exchange Link and Direct
            std::mem::swap(bor_next, bor_cur);

            ghost! {
                pa.perms.insert_ghost(snapshot!(*cur@), perm_cur.into_inner());

                let new_d = snapshot!(Int::min(pa.depth.get(*cur@), pa.depth.get(*next@) - 1));
                pa.depth = snapshot!(pa.depth.set(*cur@, *new_d))
            };
        }
    }
}

use creusot_std::{
    ghost::invariant::Tokens,
    prelude::{vec, *},
};
use implementation::PersistentArray;

#[requires(tokens.contains(implementation::PARRAY()))]
pub fn testing(mut tokens: Ghost<Tokens>) {
    let a = PersistentArray::new(vec![1, 2, 3, 4]);

    let a2 = a.set(1, 42, ghost!(tokens.reborrow()));
    let a3 = a.set(0, 50, ghost!(tokens.reborrow()));

    let a4 = a.clone();

    let a_model = snapshot!(seq![1i32, 2i32, 3i32, 4i32]);
    let a2_model = snapshot!(seq![1i32, 42i32, 3i32, 4i32]);
    let a3_model = snapshot!(seq![50i32, 2i32, 3i32, 4i32]);
    proof_assert!(a@ == *a_model);
    proof_assert!(a2@ == *a2_model);
    proof_assert!(a3@ == *a3_model);
    proof_assert!(a4@ == *a_model);
}
