extern crate creusot_contracts;

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_contracts::{
        Clone,
        cell::{PermCell, PermCellOwn},
        ghost::{
            local_invariant::{
                LocalInvariant, LocalInvariantExt as _, Protocol, Tokens, declare_namespace,
            },
            resource::fmap_view::{Authority, Fragment},
        },
        logic::{FMap, Id, Mapping},
        *,
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
        /// This contains a fragment of the map, with only `permcell.id()` as key.
        /// The corresponding value is the logical value of the map.
        frag: Ghost<Fragment<Id, Seq<T>>>,
        /// The [`Id`] in the public part is the id of the whole `GMap`, **not** the individual keys !
        inv: Ghost<Rc<LocalInvariant<PA<T>>>>,
    }

    impl<T> Clone for PersistentArray<T> {
        #[ensures(result@ == self@)]
        fn clone(&self) -> Self {
            Self {
                permcell: self.permcell.clone(),
                frag: ghost!(self.frag.clone()),
                inv: ghost!(self.inv.clone()),
            }
        }
    }

    impl<T> Invariant for PersistentArray<T> {
        #[logic]
        fn invariant(self) -> bool {
            pearlite! {
                // We indeed have the corresponding fragment of the invariant
                self.frag@.0 == self.permcell@.id()
                && self.frag.id() == self.inv@.public()
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
            pearlite! { self.frag@.1 }
        }
    }

    /// Structure describing the invariants respected by the pointers.
    struct PA<T> {
        /// Holds the permission for each pointer.
        perms: FMap<Id, PermCellOwn<Inner<T>>>,
        /// Holds the 'authoritative' version of the map of logical values.
        ///
        /// When we open the invariant, we get (a mutable borrow to) this, and can learn
        /// that some persistent array is in the map with some value.
        auth: Authority<Id, Seq<T>>,
        /// Rank: used to show that there is no cycle in our structure. Useful in `reroot`.
        depth: Snapshot<Mapping<Id, Int>>,
    }

    impl<T> Protocol for PA<T> {
        type Public = Id;

        #[logic(inline)]
        fn protocol(self, resource_id: Id) -> bool {
            pearlite! {
                self.partial_invariant(resource_id) &&
                forall<id> self.auth@.contains(id) ==> self.perms.contains(id)
            }
        }
    }

    impl<T> PA<T> {
        #[logic(inline)]
        fn partial_invariant(self, resource_id: Id) -> bool {
            pearlite! {
                self.auth.id() == resource_id &&
                forall<id> self.auth@.contains(id) && self.perms.contains(id) ==>
                    self.perms[id].id() == id &&
                    match self.perms[id].val() {
                        Inner::Direct(v) => self.auth@[id] == v@,
                        Inner::Link { index, value, next } =>
                            // If `Link { next, .. }` is in the map, then `next` is also in the map.
                            self.auth@.contains(next@.id()) &&
                            // The depth decreases when following the links
                            self.depth[id] > self.depth[next@.id()] &&
                            index@ < self.auth@[next@.id()].len() &&
                            self.auth@[id] == self.auth@[next@.id()].set(index@, *value)
                    }
            }
        }
    }

    impl<T> PersistentArray<T> {
        /// Create a new array from the given vector of values
        #[ensures(result@ == v@)]
        pub fn new(v: Vec<T>) -> Self {
            let seq = snapshot!(v@);
            let (permcell, permcellown) = PermCell::new(Inner::Direct(v));
            let mut auth = Authority::new();
            let frag = ghost!(auth.insert(snapshot!(permcellown.id()), seq));

            let inv = ghost! {
                let mut perms = FMap::new();
                perms.insert_ghost(*permcellown.id_ghost(), permcellown.into_inner());
                let local_inv = LocalInvariant::new(
                    ghost!(PA {
                        perms: perms.into_inner(),
                        auth: auth.into_inner(),
                        depth: snapshot!(|_| 0),
                    }),
                    snapshot!(frag.id()),
                    snapshot!(PARRAY()),
                );
                Rc::new(local_inv.into_inner())
            };

            Self { permcell: Rc::new(permcell), frag, inv }
        }

        /// Return a new array, where the value at index `index` has been set to `value`
        #[requires(index@ < self@.len())]
        #[requires(tokens.contains(PARRAY()))]
        #[ensures(result@ == self@.set(index@, value))]
        pub fn set(&self, index: usize, value: T, tokens: Ghost<Tokens>) -> Self {
            let new_seq = snapshot!(self@.set(index@, value));
            let (permcell, permcellown) =
                PermCell::new(Inner::Link { index, value, next: self.permcell.clone() });
            let frag = self.inv.open(tokens, |mut pa| {
                ghost! {
                    // prove that self is contained in the map by validity
                    pa.auth.contains(&self.frag);
                    // prove that we are inserting a _new_ value
                    let cell_id = permcell.id_ghost().into_inner();
                    if let Some(other) = pa.perms.get_mut_ghost(&cell_id) {
                        PermCellOwn::disjoint_lemma(other, &permcellown);
                    }
                    pa.perms.insert_ghost(cell_id, permcellown.into_inner());
                    pa.depth = snapshot!(pa.depth.set(cell_id, pa.depth[self.permcell@.id()] + 1));
                    pa.auth.insert(snapshot!(cell_id), new_seq)
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
            ghost! { pa.auth.contains(&self.frag) };
            unsafe { Self::get_inner_immut(&self.permcell, index, pa) }
        }

        #[requires(exists<p> pa.protocol(p))]
        #[requires(pa.auth@.contains(inner@.id()))]
        #[requires(i@ < pa.auth@[inner@.id()].len())]
        #[ensures(*result == pa.auth@[inner@.id()][i@])]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PermCell<Inner<T>>>,
            i: usize,
            pa: Ghost<&'a PA<T>>,
        ) -> &'a T {
            match unsafe { inner.borrow(ghost!(pa.perms.get_ghost(&*inner.id_ghost()).unwrap())) } {
                Inner::Direct(v) => &v[i],
                Inner::Link { index, value, .. } if i == *index => value,
                Inner::Link { next, .. } => Self::get_inner_immut(next, i, pa),
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
                ghost! { pa.auth.contains(&self.frag) };
                Self::reroot(&self.permcell, auth_id, ghost!(&mut *pa));
                let perm =
                    ghost!(pa.into_inner().perms.get_ghost(&self.permcell.id_ghost()).unwrap());
                let Inner::Direct(arr) = (unsafe { self.permcell.borrow(perm) }) else {
                    unreachable!()
                };
                arr.get_unchecked(index)
            })
        }

        /// Reroot the array: at the end of this function, `inner` will point directly
        /// to the underlying array.
        #[requires(pa.partial_invariant(*auth_id))]
        #[requires(pa.auth@.contains(cur@.id()))]
        #[requires(forall<id> pa.auth@.contains(id) && pa.depth[id] <= pa.depth[cur@.id()]
            ==> pa.perms.contains(id)
        )]
        #[ensures((^pa).partial_invariant(*auth_id))]
        #[ensures((^pa).auth == pa.auth)]
        #[ensures(forall<id> pa.depth[id] > pa.depth[cur@.id()] ==>
            pa.perms.get(id) == (^pa).perms.get(id) && pa.depth[id] == (^pa).depth[id])]
        #[ensures(forall<id> (^pa).perms.contains(id) == pa.perms.contains(id))]
        #[ensures(match *(^pa).perms[cur@.id()].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        fn reroot(cur: &Rc<PermCell<Inner<T>>>, auth_id: Snapshot<Id>, mut pa: Ghost<&mut PA<T>>) {
            // We take ownership of cur
            let mut perm_cur = ghost!(pa.perms.remove_ghost(&cur.id_ghost()).unwrap());
            let bor_cur = unsafe { cur.borrow_mut(ghost!(&mut perm_cur)) };

            // If we are already at the root, we are done
            let Inner::Link { next, value, index } = bor_cur else {
                ghost!(pa.perms.insert_ghost(*cur.id_ghost(), perm_cur.into_inner()));
                return;
            };

            // Recursively reroot the next node
            Self::reroot(&next, auth_id, ghost!(&mut *pa));

            // Change the next field
            let next = std::mem::replace(next, cur.clone());

            // Take the ownership of next
            let perm_next = ghost! { pa.perms.get_mut_ghost(&*next.id_ghost()).unwrap() };
            let bor_next = unsafe { next.borrow_mut(perm_next) };

            // Exchange the value field witht the content of the array
            let Inner::Direct(arr) = bor_next else { unreachable!() };
            std::mem::swap(&mut arr[*index], value);

            // Exchange Link and Direct
            std::mem::swap(bor_next, bor_cur);

            ghost! {
                pa.perms.insert_ghost(*cur.id_ghost(), perm_cur.into_inner());

                let new_d = snapshot!(Int::min(pa.depth.get(cur@.id()), pa.depth.get(next@.id()) - 1));
                pa.depth = snapshot!(pa.depth.set(cur@.id(), *new_d))
            };
        }
    }
}

use creusot_contracts::{ghost::local_invariant::Tokens, vec, *};
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
