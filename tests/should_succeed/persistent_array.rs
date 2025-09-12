// TACTIC +inline_goal
extern crate creusot_contracts;

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_contracts::{
        Clone,
        local_invariant::{
            LocalInvariant, LocalInvariantExt as _, Protocol, Tokens, declare_namespace,
        },
        logic::{FMap, Id, Mapping},
        pcell::{PCell, PCellOwn},
        resource::fmap_view::{Authority, Fragment},
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
        pcell: Rc<PCell<Inner<T>>>,
        /// Fragment of the GMap resource.
        ///
        /// This contains a fragment of the map, with only `pcell.id()` as key.
        /// The corresponding value is the logical value of the map.
        frag: Ghost<Fragment<Id, Seq<T>>>,
        /// The [`Id`] in the public part is the id of the whole `GMap`, **not** the individual keys !
        inv: Ghost<Rc<LocalInvariant<PA<T>>>>,
    }

    impl<T> Clone for PersistentArray<T> {
        #[ensures(result@ == self@)]
        fn clone(&self) -> Self {
            Self {
                pcell: self.pcell.clone(),
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
                self.frag@.0 == self.pcell@.id()
                && self.frag.id() == self.inv@.public()
                && self.inv@.namespace() == PARRAY()
            }
        }
    }

    enum Inner<T> {
        Direct(Vec<T>),
        Link { index: usize, value: T, next: Rc<PCell<Inner<T>>> },
    }

    impl<T> View for PersistentArray<T> {
        type ViewTy = Seq<T>;
        #[logic]
        fn view(self) -> Seq<T> {
            pearlite! { self.frag@.1 }
        }
    }

    /// Structure describing the invariants respected by the pointers.
    struct PA<T> {
        /// Holds the permission for each pointer.
        perms: FMap<Id, PCellOwn<Inner<T>>>,
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

        #[logic]
        fn protocol(self, resource_id: Id) -> bool {
            pearlite! {
                self.auth.id() == resource_id &&
                forall<id> self.auth@.contains(id) ==>
                    self.perms.contains(id) &&
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
            let (pcell, pcellown) = PCell::new(Inner::Direct(v));
            let mut auth = Authority::new();
            let frag = ghost!(auth.insert(snapshot!(pcellown.id()), seq));

            let inv = ghost! {
                let mut perms = FMap::new();
                perms.insert_ghost(*pcellown.id_ghost(), pcellown.into_inner());
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

            Self { pcell: Rc::new(pcell), frag, inv }
        }

        /// Return a new array, where the value at index `index` has been set to `value`
        #[requires(index@ < self@.len())]
        #[requires(tokens.contains(PARRAY()))]
        #[ensures(result@ == self@.set(index@, value))]
        pub fn set(&self, index: usize, value: T, tokens: Ghost<Tokens>) -> Self {
            let new_seq = snapshot!(self@.set(index@, value));
            let (pcell, pcellown) =
                PCell::new(Inner::Link { index, value, next: self.pcell.clone() });
            let frag = self.inv.open(tokens, |mut pa| {
                ghost! {
                    // prove that self is contained in the map by validity
                    pa.auth.contains(&self.frag);
                    // prove that we are inserting a _new_ value
                    let cell_id = pcell.id_ghost().into_inner();
                    if let Some(other) = pa.perms.get_mut_ghost(&cell_id) {
                        PCellOwn::disjoint_lemma(other, &pcellown);
                    }
                    pa.perms.insert_ghost(cell_id, pcellown.into_inner());
                    pa.depth = snapshot!(pa.depth.set(cell_id, pa.depth[self.pcell@.id()] + 1));
                    pa.auth.insert(snapshot!(cell_id), new_seq)
                }
            });
            Self { pcell: Rc::new(pcell), frag, inv: ghost!(self.inv.clone()) }
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
        pub unsafe fn get_immut<'a>(&'a self, index: usize, tokens: Ghost<Tokens<'a>>) -> &'a T {
            self.inv.open(tokens, |pa| {
                // prove that self is contained in the map by validity
                ghost! { pa.auth.contains(&self.frag) };
                unsafe { Self::get_inner_immut(&self.pcell, index, ghost!(pa.into_inner())) }
            })
        }

        #[requires(exists<p> inv.protocol(p))]
        #[requires(inv.auth@.contains(inner@.id()))]
        #[requires(i@ < inv.auth@[inner@.id()].len())]
        #[ensures(*result == inv.auth@[inner@.id()][i@])]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PCell<Inner<T>>>,
            i: usize,
            inv: Ghost<&'a PA<T>>,
        ) -> &'a T {
            let perm = ghost!(inv.perms.get_ghost(&*inner.id_ghost()).unwrap());
            match unsafe { inner.borrow(perm) } {
                Inner::Direct(v) => &v[i],
                Inner::Link { index, value, .. } if i == *index => value,
                Inner::Link { next, .. } => Self::get_inner_immut(next, i, inv),
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
                Self::reroot(&self.pcell, auth_id, ghost!(&mut *pa));
                let perm = ghost!(pa.into_inner().perms.get_ghost(&self.pcell.id_ghost()).unwrap());
                let Inner::Direct(arr) = (unsafe { self.pcell.borrow(perm) }) else {
                    unreachable!()
                };
                arr.get_unchecked(index)
            })
        }

        /// Reroot the array: at the end of this function, `inner` will point directly
        /// to the underlying array.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(pa.protocol(*auth_id))]
        #[requires(pa.auth@.contains(inner@.id()))]
        #[ensures((^pa).protocol(*auth_id))]
        #[ensures((^pa).auth == pa.auth)]
        #[ensures(forall<id> pa.depth[id] > pa.depth[inner@.id()]
            ==> pa.perms.get(id) == (^pa).perms.get(id)
        )]
        #[ensures(match *(^pa).perms[inner@.id()].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        fn reroot(inner: &Rc<PCell<Inner<T>>>, auth_id: Snapshot<Id>, mut pa: Ghost<&mut PA<T>>) {
            let id = inner.id_ghost();
            let perm = ghost!(pa.perms.get_ghost(&*id).unwrap());
            let Inner::Link { next, .. } = (unsafe { inner.borrow(perm) }) else { return };

            let next = next.clone(); // FIXME: unnecessary clone
            Self::reroot(&next, auth_id, ghost!(&mut *pa));

            let (perm_inner, mut rest) = ghost!(pa.perms.split_mut_ghost(&id)).split();
            let perm_next = ghost! { rest.get_mut_ghost(&*next.id_ghost()).unwrap() };
            let bor_inner = unsafe { inner.borrow_mut(perm_inner) };
            let bor_next = unsafe { next.borrow_mut(perm_next) };

            // This breaks the invariant: now `next` points to itself
            std::mem::swap(bor_inner, bor_next);

            // Restore the invariant
            let (Inner::Direct(arr), Inner::Link { index, value: value_next, next: next_next }) =
                (bor_inner, bor_next)
            else {
                unreachable!()
            };

            *next_next = inner.clone();
            std::mem::swap(&mut arr[*index], value_next);
            let next_d = snapshot!(pa.depth.get(next@.id()));
            let new_d = snapshot!(Int::min(pa.depth.get(*id), *next_d - 1));
            ghost! { pa.depth = snapshot!(pa.depth.set(*id, *new_d)) };
        }
    }
}

use creusot_contracts::{local_invariant::Tokens, vec, *};
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
