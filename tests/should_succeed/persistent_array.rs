extern crate creusot_contracts;

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_contracts::{
        Clone,
        local_invariant::{
            LocalInvariant, LocalInvariantExt as _, LocalInvariantSpec, Tokens, declare_namespace,
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
        program_value: Rc<PCell<Inner<T>>>,
        /// Fraction of the GMap resource.
        ///
        /// This contains a fraction of the map, with only `program_value.id()` as key.
        /// The corresponding value is the logical value of the map.
        contained_in_inv: Ghost<Rc<Fragment<Id, Seq<T>>>>,
        /// The [`Id`] in the public part is the id of the whole `GMap`, **not** the individual keys !
        map_invariant: Ghost<Rc<LocalInvariant<PA<T>>>>,
    }

    impl<T> Clone for PersistentArray<T> {
        #[ensures(result@ == self@)]
        fn clone(&self) -> Self {
            Self {
                program_value: self.program_value.clone(),
                contained_in_inv: self.contained_in_inv.clone(),
                map_invariant: self.map_invariant.clone(),
            }
        }
    }

    impl<T> Invariant for PersistentArray<T> {
        #[logic]
        fn invariant(self) -> bool {
            pearlite! {
                // We indeed have the corresponding fractional part of the invariant
                self.contained_in_inv@@.0 == self.program_value@.id()
                && self.contained_in_inv@.id() == self.map_invariant@.public()
                && self.map_invariant@.namespace() == PARRAY()
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
            pearlite! {
                self.contained_in_inv@@.1
            }
        }
    }

    /// Structure describing the invariants respected by the pointers.
    struct PA<T> {
        /// Holds the permission for each pointer.
        permissions: FMap<Id, PCellOwn<Inner<T>>>,
        /// Holds the 'authoritative' version of the map of logical values.
        ///
        /// When we open the invariant, we get (a mutable borrow to) this, and can learn
        /// that some persistent array is in the map with some value.
        auth: Authority<Id, Seq<T>>,
        /// Rank: used to show that there is no cycle in our structure. Useful in `reroot`.
        rank: Snapshot<Mapping<Id, Int>>,
        /// Common length of the arrays managed by this map.
        length: Snapshot<Int>,
    }

    impl<T> LocalInvariantSpec for PA<T> {
        type Public = Id;

        #[logic]
        fn invariant_with_data(self, resource_id: Id) -> bool {
            pearlite! {
                self.auth.id() == resource_id &&
                forall<id> self.auth@.contains(id) ==>
                    self.permissions.contains(id) &&
                    self.permissions[id].id() == id &&
                    self.auth@[id].len() == *self.length &&
                    match *self.permissions[id].val() {
                        Inner::Direct(v) => self.auth@[id] == v@,
                        Inner::Link { index, value, next } => {
                            // If `Link { next, .. }` is in the map, then `next` is also in the map.
                            self.auth@.contains(next@.id()) &&
                            // The rank decreases when following the links
                            self.rank[id] > self.rank[next@.id()] &&
                            index@ < *self.length &&
                            self.auth@[id] == self.auth@[next@.id()].set(index@, value)
                        },
                    }
            }
        }
    }

    impl<T> PersistentArray<T> {
        /// Create a new array from the given vector of values
        #[ensures(result@ == v@)]
        pub fn new(v: Vec<T>) -> Self {
            let logical_value = snapshot!(v@);
            let (program_value, ownership) = PCell::new(Inner::Direct(v));
            let id = snapshot!(ownership.id());
            let length = snapshot!(logical_value.len());
            let mut resource = Authority::new();
            let frac_part = ghost!(resource.insert(id, logical_value));
            let gset_id = snapshot!(frac_part.id());

            let map_invariant = ghost! {
                let mut permissions = FMap::new();
                permissions.insert_ghost(id.into_ghost().into_inner(), ownership.into_inner());
                let local_inv = LocalInvariant::new(
                    ghost!(PA {
                        permissions: permissions.into_inner(),
                        auth: resource.into_inner(),
                        rank: snapshot!(|_| 0),
                        length,
                    }),
                    snapshot!(*gset_id),
                    snapshot!(PARRAY()),
                );
                Rc::new(local_inv.into_inner())
            };

            Self {
                program_value: Rc::new(program_value),
                contained_in_inv: ghost!(Rc::new(frac_part.into_inner())),
                map_invariant,
            }
        }

        /// Return a new array, where the value at index `index` has been set to `value`
        #[requires(index@ < self@.len())]
        #[requires(tokens.contains(PARRAY()))]
        #[ensures(result@ == self@.set(index@, value))]
        pub fn set(&self, index: usize, value: T, tokens: Ghost<Tokens>) -> Self {
            let new_logical_value = snapshot!(self@.set(index@, value));
            let (program_value, ownership) =
                PCell::new(Inner::Link { index, value, next: self.program_value.clone() });
            let new_frac = {
                let program_value = &program_value;
                self.map_invariant.borrow().open(tokens, |mut inv| {
                    ghost! {
                        let cell_id = program_value.id_ghost().into_inner();
                        let self_id = snapshot!(self.program_value@.id());
                        // prove that self is contained in the map by validity
                        inv.auth.contains(self.contained_in_inv.as_ref());
                        // prove that we are inserting a _new_ value
                        let ownership = ownership.into_inner();
                        match inv.permissions.get_mut_ghost(&cell_id) {
                            None => {},
                            Some(other) => PCellOwn::disjoint_lemma(other, &ownership),
                        }
                        inv.permissions.insert_ghost(cell_id, ownership);
                        inv.rank = snapshot! {
                            let new_distance = inv.rank[*self_id] + 1;
                            inv.rank.set(cell_id, new_distance)
                        };
                        let frac = inv.auth.insert(snapshot!(cell_id), new_logical_value);
                        Rc::new(frac)
                    }
                })
            };
            Self {
                program_value: Rc::new(program_value),
                contained_in_inv: new_frac,
                map_invariant: self.map_invariant.clone(),
            }
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
            self.map_invariant.borrow().open(tokens, |inv| {
                // prove that self is contained in the map by validity
                ghost! {
                    inv.auth.contains(self.contained_in_inv.as_ref());
                };
                unsafe {
                    Self::get_inner_immut(&self.program_value, index, ghost!(inv.into_inner()))
                }
            })
        }

        #[requires(exists<p> inv.invariant_with_data(p))]
        #[requires(inv.auth@.contains(inner@.id()))]
        #[requires(i@ < inv.auth@[inner@.id()].len())]
        #[ensures(*result == inv.auth@[inner@.id()][i@])]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PCell<Inner<T>>>,
            i: usize,
            inv: Ghost<&'a PA<T>>,
        ) -> &'a T {
            let perm = ghost!(inv.permissions.get_ghost(&*inner.id_ghost()).unwrap());
            let inner = unsafe { inner.as_ref().borrow(perm) };
            match inner {
                Inner::Direct(v) => &v[i],
                Inner::Link { index, value, next } => {
                    if i == *index {
                        value
                    } else {
                        Self::get_inner_immut(next, i, inv)
                    }
                }
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
            let public = snapshot!(self.map_invariant@.public());
            self.map_invariant.borrow().open(tokens, |mut inv| {
                // prove that self is contained in the map by validity
                ghost! {
                    inv.auth.contains(self.contained_in_inv.as_ref());
                };
                unsafe { Self::reroot(&self.program_value, public, ghost!(&mut *inv)) };
                let id = self.program_value.id_ghost();
                let perm = ghost!(inv.into_inner().permissions.get_ghost(&*id).unwrap());
                let borrow = unsafe { self.program_value.as_ref().borrow(perm) };
                match borrow {
                    Inner::Direct(arr) => arr.get_unchecked(index),
                    _ => unreachable!(),
                }
            })
        }

        /// Reroot the array: at the end of this function, `inner` will point directly
        /// to the underlying array.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(inv.invariant_with_data(*invariant_id))]
        #[requires(inv.auth@.contains(inner@.id()))]
        #[ensures((^inv.inner_logic()).invariant_with_data(*invariant_id))]
        #[ensures(forall<id> (*inv).auth@.contains(id) == (^inv.inner_logic()).auth@.contains(id))]
        #[ensures((*inv).auth == (^inv.inner_logic()).auth)]
        #[ensures((*inv).length == (^inv.inner_logic()).length)]
        #[ensures(forall<id> (*inv).rank[id] > (*inv).rank[inner@.id()]
            ==> (*inv).rank[id] == (^inv.inner_logic()).rank[id]
            && (*inv).permissions.get(id) == (^inv.inner_logic()).permissions.get(id)
        )]
        #[ensures(match *(^inv.inner_logic()).permissions[inner@.id()].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        #[ensures(*result == (^inv.inner_logic()).rank[inner@.id()])]
        unsafe fn reroot<'a>(
            inner: &'a Rc<PCell<Inner<T>>>,
            invariant_id: Snapshot<Id>,
            mut inv: Ghost<&'a mut PA<T>>,
        ) -> Snapshot<Int> {
            let inner_clone = inner.clone();
            let id = inner.id_ghost();
            let rank = snapshot!(inv.rank.get(*id));
            let perm = ghost!(inv.permissions.get_ghost(&*id).unwrap());
            let borrow = unsafe { inner.as_ref().borrow(perm) };
            match borrow {
                Inner::Direct(_) => {
                    snapshot!(inv.rank[*id])
                }
                Inner::Link { next, .. } => {
                    let next = next.clone();
                    let next_id = next.id_ghost();
                    let next_d = Self::reroot(&next, invariant_id, ghost!(&mut *inv));

                    let (perm_inner, perm_next) = ghost! {
                        let (p_inner, rest) = inv.permissions.split_mut_ghost(&id);
                        (p_inner, rest.get_mut_ghost(&*next_id).unwrap())
                    }
                    .split();
                    let (bor_inner, bor_next) = unsafe {
                        (inner.as_ref().borrow_mut(perm_inner), next.as_ref().borrow_mut(perm_next))
                    };

                    // This breaks the invariant: now `next` points to itself
                    std::mem::swap(bor_inner, bor_next);

                    // Restore the invariant
                    match (bor_inner, bor_next) {
                        (Inner::Direct(arr), Inner::Link { index, value: value_next, next }) => {
                            *next = inner_clone;
                            std::mem::swap(&mut arr[*index], value_next);
                            let new_d = snapshot!(Int::min(*rank, *next_d - 1));
                            ghost! { inv.rank = snapshot!(inv.rank.set(*id, *new_d)) };
                            new_d
                        }
                        _ => unreachable!(),
                    }
                }
            }
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
