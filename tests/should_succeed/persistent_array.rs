extern crate creusot_contracts;

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_contracts::{
        Clone,
        local_invariant::{
            LocalInvariant, LocalInvariantExt as _, LocalInvariantSpec, Namespaces,
            declare_namespace,
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
    /// If you don't, you must ensure that a [`TokensMap`] object is never used with a
    /// `PersistentArray` that is not derived from it.
    pub struct PersistentArray<T> {
        /// Contains a pointer to the actual value
        program_value: Rc<PCell<Inner<T>>>,
        /// Fraction of the GMap resource.
        ///
        /// This contains a fraction of the map, with only `program_value.id()` as key.
        /// The corresponding value is the logical value of the map.
        contained_in_token: Ghost<Rc<Fragment<Id, Seq<T>>>>,
        /// The [`Id`] in the public part is the id of the whole `GMap`, **not** the individual keys !
        map_invariant: Ghost<Rc<LocalInvariant<CompleteMap<T>>>>,
    }

    impl<T> Clone for PersistentArray<T> {
        #[ensures(result@ == self@)]
        fn clone(&self) -> Self {
            Self {
                program_value: self.program_value.clone(),
                contained_in_token: self.contained_in_token.clone(),
                map_invariant: self.map_invariant.clone(),
            }
        }
    }

    impl<T> Invariant for PersistentArray<T> {
        #[logic]
        fn invariant(self) -> bool {
            pearlite! {
                // We indeed have the corresponding fractional part of the invariant
                self.contained_in_token@@.0 == self.program_value@.id()
                && self.contained_in_token@.id() == self.map_invariant@.public()
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
                self.contained_in_token@@.1
            }
        }
    }

    /// Structure describing the invariants respected by the pointers.
    struct CompleteMap<T> {
        /// Holds the permission for each pointer.
        own_map: FMap<Snapshot<Id>, PCellOwn<Inner<T>>>,
        /// Holds the 'authoritative' version of the map of logical values.
        ///
        /// When we open the invariant, we get (a mutable borrow to) this, and can learn
        /// that some persistent array is in the map with some value.
        values: Authority<Id, Seq<T>>,
        /// Rank: used to show that there is no cycle in our structure. Useful in `reroot`.
        rank: Snapshot<Mapping<Id, Int>>,
        /// Common length of the arrays managed by this map.
        length: Snapshot<Int>,
    }

    impl<T> LocalInvariantSpec for CompleteMap<T> {
        type Public = Id;

        #[logic]
        fn invariant_with_data(self, id: Id) -> bool {
            pearlite! {
                self.values.id() == id &&
                (forall<id> self.own_map.contains(id) == self.values@.contains(*id)) &&
                (forall<id> self.own_map.contains(id) ==> self.own_map[id].id() == *id) &&
                (forall<id> self.own_map.contains(id) ==> self.values@.lookup(*id).len() == *self.length) &&
                // If `Link { next, .. }` is in the map, then `next` is also in the map.
                (forall<id> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(_) => true,
                    Inner::Link { next, .. } => self.own_map.contains(Snapshot::new(next@.id())),
                }) &&
                // The array in `self.values` agrees with the one in `self.own_map`
                (forall<id> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(v) => self.values@.lookup(*id) == v@,
                    Inner::Link { index, value, next } => {
                        let next_id = next@.id();
                        index@ < *self.length &&
                        self.values@.lookup(*id)[index@] == value &&
                        (forall<j: Int> 0 <= j && j < *self.length && j != index@ ==> self.values@.lookup(*id)[j] == self.values@.lookup(next_id)[j])
                    },
                }) &&
                // The rank decreases when following the links
                (forall<id> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(_) => true,
                    Inner::Link { next, .. } => {
                        let next_id = next@.id();
                        self.rank[*id] > self.rank[next_id]
                    },
                })
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
                let mut own_map = FMap::new();
                own_map.insert_ghost(id, ownership.into_inner());
                let local_inv = LocalInvariant::new(
                    ghost!(CompleteMap {
                        own_map: own_map.into_inner(),
                        values: resource.into_inner(),
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
                contained_in_token: ghost!(Rc::new(frac_part.into_inner())),
                map_invariant,
            }
        }

        /// Return a new array, where the value at index `index` has been set to `value`
        #[requires(index@ < self@.len())]
        #[requires(namespaces.contains(PARRAY()))]
        #[ensures(result@ == self@.set(index@, value))]
        pub fn set(&self, index: usize, value: T, namespaces: Ghost<Namespaces>) -> Self {
            let new_logical_value = snapshot!(self@.set(index@, value));
            let (program_value, ownership) =
                PCell::new(Inner::Link { index, value, next: self.program_value.clone() });
            let new_frac = {
                let program_value = &program_value;
                self.map_invariant.borrow().open(namespaces, |mut tokens| {
                    let cell_id = snapshot!(program_value.id());
                    let self_id = snapshot!(self.program_value@.id());
                    ghost! {
                        // prove that self is contained in the map by validity
                        tokens.values.contains(self.contained_in_token.as_ref());
                        // prove that we are inserting a _new_ value
                        let ownership = ownership.into_inner();
                        match tokens.own_map.get_mut_ghost(&cell_id) {
                            None => {},
                            Some(other) => PCellOwn::disjoint_lemma(other, &ownership),
                        }
                        tokens.own_map.insert_ghost(cell_id, ownership);
                        tokens.rank = snapshot! {
                            let new_distance = tokens.rank[*self_id] + 1;
                            tokens.rank.set(*cell_id, new_distance)
                        };
                        let frac = tokens.values.insert(cell_id, new_logical_value);
                        Rc::new(frac)
                    }
                })
            };
            Self {
                program_value: Rc::new(program_value),
                contained_in_token: new_frac,
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
        #[requires(namespaces.contains(PARRAY()))]
        #[ensures(result == if i@ < self@.len() {
            Some(&self@[i@])
        } else {
            None
        })]
        pub unsafe fn get_immut<'a>(
            &'a self,
            i: usize,
            namespaces: Ghost<Namespaces<'a>>,
        ) -> Option<&'a T> {
            self.map_invariant.borrow().open(namespaces, |tokens| {
                // prove that self is contained in the map by validity
                ghost! {
                    tokens.values.contains(self.contained_in_token.as_ref());
                };
                unsafe {
                    Self::get_inner_immut(&self.program_value, i, ghost!(tokens.into_inner()))
                }
            })
        }

        #[requires(exists<p> tokens.invariant_with_data(p))]
        #[requires(tokens.own_map.contains(Snapshot::new(inner.view().id())))]
        #[ensures(if i.view() < *tokens.length {
            result == Some(&tokens.values@[inner.view().id()][i.view()])
        } else {
            result == None
        })]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PCell<Inner<T>>>,
            i: usize,
            tokens: Ghost<&'a CompleteMap<T>>,
        ) -> Option<&'a T> {
            let id = snapshot!(inner.view().id());
            let perm = ghost!(tokens.own_map.get_ghost(&id).unwrap());
            let inner = unsafe { inner.as_ref().borrow(perm) };
            match inner {
                Inner::Direct(v) => match v.get(i) {
                    None => None,
                    Some(x) => Some(x),
                },
                Inner::Link { index, value, next } => {
                    if i == *index {
                        Some(value)
                    } else {
                        Self::get_inner_immut(next, i, tokens)
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
        #[requires(namespaces.contains(PARRAY()))]
        #[ensures(if index.view() < self.view().len() {
            result == Some(&self.view()[index.view()])
        } else {
            result == None
        })]
        pub unsafe fn get<'a>(
            &'a self,
            index: usize,
            namespaces: Ghost<Namespaces<'a>>,
        ) -> Option<&'a T> {
            let public = snapshot!(self.map_invariant@.public());
            self.map_invariant.borrow().open(namespaces, |mut tokens| {
                // prove that self is contained in the map by validity
                ghost! {
                    tokens.values.contains(self.contained_in_token.as_ref());
                };
                unsafe { Self::reroot(&self.program_value, public, ghost!(&mut *tokens)) };
                let id = snapshot!(self.program_value.view().id());
                let perm = ghost!(tokens.into_inner().own_map.get_ghost(&id).unwrap());
                let borrow = unsafe { self.program_value.as_ref().borrow(perm) };
                match borrow {
                    Inner::Direct(arr) => arr.get(index),
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
        #[requires(tokens.invariant_with_data(*invariant_id))]
        #[requires(tokens.own_map.contains(Snapshot::new(inner.view().id())))]
        #[ensures((^tokens.inner_logic()).invariant_with_data(*invariant_id))]
        #[ensures(forall<id> (*tokens).own_map.contains(id) == (^tokens.inner_logic()).own_map.contains(id))]
        #[ensures((*tokens).values == (^tokens.inner_logic()).values)]
        #[ensures((*tokens).length == (^tokens.inner_logic()).length)]
        #[ensures(forall<id: Snapshot<_>> (*tokens).rank[*id] > (*tokens).rank[inner.view().id()]
            ==> (*tokens).rank[*id] == (^tokens.inner_logic()).rank[*id]
            && (*tokens).own_map.get(id) == (^tokens.inner_logic()).own_map.get(id)
        )]
        #[ensures(match *(^tokens.inner_logic()).own_map[Snapshot::new(inner.view().id())].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        #[ensures(*result == (^tokens.inner_logic()).rank[inner.view().id()])]
        unsafe fn reroot<'a>(
            inner: &'a Rc<PCell<Inner<T>>>,
            invariant_id: Snapshot<Id>,
            mut tokens: Ghost<&'a mut CompleteMap<T>>,
        ) -> Snapshot<Int> {
            let inner_clone = inner.clone();
            let id = snapshot!(inner.view().id());
            let rank = snapshot!(tokens.rank.get(*id));
            let perm = ghost!(tokens.own_map.get_ghost(&id).unwrap());
            let borrow = unsafe { inner.as_ref().borrow(perm) };
            match borrow {
                Inner::Direct(_) => {
                    snapshot!(tokens.rank[*id])
                }
                Inner::Link { next, .. } => {
                    let next = next.clone();
                    let next_id = snapshot!(next.view().id());
                    let next_d = Self::reroot(&next, invariant_id, ghost!(&mut *tokens));

                    let (perm_inner, perm_next) = ghost! {
                        let (p_inner, rest) = tokens.own_map.split_mut_ghost(&id);
                        (p_inner.unwrap(), rest.get_mut_ghost(&next_id).unwrap())
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
                            ghost! { tokens.rank = snapshot!(tokens.rank.set(*id, *new_d)) };
                            new_d
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
    }
}

use creusot_contracts::{local_invariant::Namespaces, vec, *};
use implementation::PersistentArray;

#[requires(namespaces.contains(implementation::PARRAY()))]
pub fn testing(mut namespaces: Ghost<Namespaces>) {
    let a = PersistentArray::new(vec![1, 2, 3, 4]);

    let a2 = a.set(1, 42, ghost!(namespaces.reborrow()));
    let a3 = a.set(0, 50, ghost!(namespaces.reborrow()));

    let a4 = a.clone();

    let a_model = snapshot!(seq![1i32, 2i32, 3i32, 4i32]);
    let a2_model = snapshot!(seq![1i32, 42i32, 3i32, 4i32]);
    let a3_model = snapshot!(seq![50i32, 2i32, 3i32, 4i32]);
    proof_assert!(a@ == *a_model);
    proof_assert!(a2@ == *a2_model);
    proof_assert!(a3@ == *a3_model);
    proof_assert!(a4@ == *a_model);
}
