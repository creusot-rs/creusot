// TACTIC +compute_in_goal

#![cfg_attr(not(creusot), feature(stmt_expr_attributes, proc_macro_hygiene))]

extern crate creusot_contracts;

// FIXME:
// - Use polymorphism rather than a fixed `Value` type
// - Wrap the `TokensMap` in a `Ghost` at each call site.
//   This is currently not possible, due to a poor interaction with type invariants.

pub mod implementation {
    use ::std::rc::Rc;
    use creusot_contracts::{
        Clone,
        logic::{FMap, Mapping},
        pcell::{PCell, PCellOwn},
        *,
    };

    /// Type of values stored in the array
    // TODO: replace with polymorphism
    type Value = i32;

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
    pub struct PersistentArray {
        /// Contains the view of the value
        logical_value: Snapshot<Seq<Value>>,
        /// Contains a pointer to the actual value
        program_value: Rc<PCell<Inner>>,
    }

    impl Clone for PersistentArray {
        #[ensures(result@ == (*self)@)]
        fn clone(&self) -> Self {
            Self { logical_value: self.logical_value, program_value: self.program_value.clone() }
        }
    }

    enum Inner {
        Direct(Vec<Value>),
        Link { index: usize, value: Value, next: Rc<PCell<Inner>> },
    }

    impl View for PersistentArray {
        type ViewTy = Seq<Value>;
        #[logic]
        fn view(self) -> Seq<Value> {
            *self.logical_value
        }
    }

    type LogicId = Snapshot<logic::Id>;
    type OwnMap = FMap<LogicId, PCellOwn<Inner>>;

    /// The ghost ownership of a family of [`PersistentArray`]s.
    pub struct TokensMap(TokensMapInner);

    /// Actual structure of the map, but without the invariant
    struct TokensMapInner {
        own_map: Ghost<OwnMap>,
        values: Snapshot<Mapping<logic::Id, Seq<Value>>>,
        rank: Snapshot<Mapping<logic::Id, Int>>,
        length: Snapshot<Int>,
    }

    impl Invariant for TokensMap {
        #[logic]
        fn invariant(self) -> bool {
            self.0.invariant_inner()
        }
    }

    impl TokensMapInner {
        #[logic]
        fn invariant_inner(self) -> bool {
            pearlite! {
                (forall<id: LogicId> self.own_map.contains(id) ==> self.own_map[id].id() == *id) &&
                (forall<id: LogicId> self.own_map.contains(id) ==> self.values[*id].len() == *self.length) &&
                // If `Link { next, .. }` is in the map, then `next` is also in the map.
                (forall<id: LogicId> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(_) => true,
                    Inner::Link { next, .. } => self.own_map.contains(Snapshot::new(next.view().id())),
                }) &&
                // The array in `self.values` agrees with the one in `self.own_map`
                (forall<id: LogicId> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(v) => self.values[*id] == v.view(),
                    Inner::Link { index, value, next } => {
                        let next_id = next.view().id();
                        index.view() < *self.length &&
                        self.values[*id][index.view()] == value &&
                        (forall<j: Int> 0 <= j && j < *self.length && j != index.view() ==> self.values[*id][j] == self.values[next_id][j])
                    },
                }) &&
                // The rank decreases when following the links
                (forall<id: LogicId> self.own_map.contains(id) ==> match *self.own_map[id].val() {
                    Inner::Direct(_) => true,
                    Inner::Link { next, .. } => {
                        let next_id = next.view().id();
                        self.rank[*id] > self.rank[next_id]
                    },
                })
            }
        }
    }

    impl TokensMap {
        /// `true` if a given `array` is managed by this map.
        #[logic]
        pub fn contains(self, array: PersistentArray) -> bool {
            let id = Snapshot::new(array.program_value.view().id());
            self.0.own_map.contains(id) && self.0.values[*id] == *array.logical_value
        }

        /// Common length of all the contained arrays
        #[logic]
        #[requires(inv(self))]
        #[ensures(forall<a> self.contains(a) ==> result == a.view().len())]
        pub fn length(self) -> Int {
            *self.0.length
        }
    }

    impl PersistentArray {
        /// Create a new array from the given vector of values
        #[ensures(result.1.contains(result.0))]
        #[ensures(result.0.view() == v.view())]
        #[ensures(result.1.length() == v.view().len())]
        pub fn new(v: Vec<Value>) -> (Self, TokensMap) {
            let logical_value = snapshot!(v.view());
            let (program_value, ownership) = PCell::new(Inner::Direct(v));
            let this = Self { logical_value, program_value: Rc::new(program_value) };
            let id = snapshot!(this.program_value.view().id());
            let mut own_map = FMap::new();
            ghost!(own_map.insert_ghost(id, ownership.into_inner()));
            let values = snapshot!(|i| if i == *id { *logical_value } else { Seq::empty() });
            let rank = snapshot!(|_| 0);
            let length = snapshot!(logical_value.len());
            let map = TokensMap(TokensMapInner { own_map, values, rank, length });

            (this, map)
        }

        /// Returns a new array, where the value at index `index` has been set to `value`
        #[requires(tokens.contains(*self))]
        #[requires(index.view() < (*tokens).length())]
        #[ensures(forall<p: Self> (*tokens).contains(p) ==> (^tokens).contains(p))]
        #[ensures((^tokens).contains(result))]
        #[ensures(result.view() == self.view().set(index.view(), value))]
        pub fn set(&self, index: usize, value: Value, mut tokens: &mut TokensMap) -> Self {
            let logical_value = snapshot!(self.logical_value.set(index.view(), value));
            let (program_value, ownership) =
                PCell::new(Inner::Link { index, value, next: self.program_value.clone() });
            let self_id = snapshot!(self.program_value.view().id());
            let id = snapshot!(program_value.id());
            let tokens = &mut tokens.0;
            ghost! {
                let mut map = tokens.own_map.borrow_mut();
                // prove that we are inserting a _new_ value
                match map.get_mut_ghost(&id) {
                    None => {},
                    Some(other) => PCellOwn::disjoint_lemma(other, &ownership),
                }
                map.insert_ghost(id, ownership.into_inner());
                tokens.values = snapshot!(tokens.values.set(*id, *logical_value));
                tokens.rank = snapshot! {
                    let new_distance = tokens.rank[*self_id] + 1;
                    tokens.rank.set(*id, new_distance)
                };
            };
            Self { logical_value, program_value: Rc::new(program_value) }
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
        #[requires(tokens.contains(*self))]
        #[ensures(if i.view() < self.view().len() {
            result == Some(&self.view()[i.view()])
        } else {
            result == None
        })]
        pub unsafe fn get_immut<'a>(
            &'a self,
            i: usize,
            tokens: &'a TokensMap,
        ) -> Option<&'a Value> {
            unsafe { Self::get_inner_immut(&self.program_value, i, tokens) }
        }

        #[requires(tokens.0.own_map.contains(Snapshot::new(inner.view().id())))]
        #[ensures(if i.view() < *tokens.0.length {
            result == Some(&tokens.0.values[inner.view().id()][i.view()])
        } else {
            result == None
        })]
        unsafe fn get_inner_immut<'a>(
            inner: &'a Rc<PCell<Inner>>,
            i: usize,
            tokens: &'a TokensMap,
        ) -> Option<&'a Value> {
            let id = snapshot!(inner.view().id());
            let perm = ghost!(tokens.0.own_map.borrow().get_ghost(&id).unwrap());
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
        #[requires(tokens.contains(*self))]
        #[ensures(if index.view() < self.view().len() {
            result == Some(&self.view()[index.view()])
        } else {
            result == None
        })]
        #[ensures(forall<a> (*tokens).contains(a) == (^tokens).contains(a))]
        #[ensures((*tokens).length() == (^tokens).length())]
        pub unsafe fn get<'a>(
            &'a self,
            index: usize,
            tokens: &'a mut TokensMap,
        ) -> Option<&'a Value> {
            unsafe { Self::reroot(&self.program_value, tokens) };
            let id = snapshot!(self.program_value.view().id());
            let perm = ghost!(tokens.0.own_map.get_ghost(&id).unwrap());
            let borrow = unsafe { self.program_value.as_ref().borrow(perm) };
            match borrow {
                Inner::Direct(arr) => arr.get(index),
                _ => unreachable!(),
            }
        }

        /// Reroot the array: at the end of this function, `inner` will point directly
        /// to the underlying array.
        ///
        /// # Safety
        ///
        /// See the [safety section](PersistentArray#safety) on the type documentation.
        #[requires(tokens.0.own_map.contains(Snapshot::new(inner.view().id())))]
        #[ensures(forall<id> (*tokens).0.own_map.contains(id) == (^tokens).0.own_map.contains(id))]
        #[ensures((*tokens).0.values == (^tokens).0.values)]
        #[ensures((*tokens).0.length == (^tokens).0.length)]
        #[ensures(forall<id: Snapshot<_>> (*tokens).0.rank[*id] > (*tokens).0.rank[inner.view().id()]
            ==> (*tokens).0.rank[*id] == (^tokens).0.rank[*id]
             && (*tokens).0.own_map.get(id) == (^tokens).0.own_map.get(id)
        )]
        #[ensures(match *(^tokens).0.own_map[Snapshot::new(inner.view().id())].val() {
            Inner::Direct(_) => true,
            Inner::Link { .. } => false,
        })]
        #[ensures(*result == (^tokens).0.rank[inner.view().id()])]
        unsafe fn reroot<'a>(
            inner: &'a Rc<PCell<Inner>>,
            tokens: &'a mut TokensMap,
        ) -> Snapshot<Int> {
            let inner_clone = inner.clone();
            let id = snapshot!(inner.view().id());
            let rank = snapshot!(tokens.0.rank.get(*id));
            let perm = ghost!(tokens.0.own_map.get_ghost(&id).unwrap());
            let borrow = unsafe { inner.as_ref().borrow(perm) };
            match borrow {
                Inner::Direct(_) => {
                    snapshot!(tokens.0.rank[*id])
                }
                Inner::Link { next, .. } => {
                    let next = next.clone();
                    let next_id = snapshot!(next.view().id());
                    let next_d = Self::reroot(&next, tokens);

                    let (perm_inner, perm_next) = ghost! {
                        let (p_inner, rest) = tokens.0.own_map.split_mut_ghost(&id);
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
                            tokens.0.rank = snapshot!(tokens.0.rank.set(*id, *new_d));
                            new_d
                        }
                        _ => unreachable!(),
                    }
                }
            }
        }
    }
}

use creusot_contracts::{vec, *};
use implementation::PersistentArray;

pub fn testing() {
    let (a, mut perm) = PersistentArray::new(vec![1, 2, 3, 4]);

    let a2 = a.set(1, 42, &mut perm);
    let a3 = a.set(0, 50, &mut perm);

    let a4 = a.clone();

    let a_model = snapshot!(seq![1i32, 2i32, 3i32, 4i32]);
    let a2_model = snapshot!(seq![1i32, 42i32, 3i32, 4i32]);
    let a3_model = snapshot!(seq![50i32, 2i32, 3i32, 4i32]);
    proof_assert!(a@ == *a_model);
    proof_assert!(a2@ == *a2_model);
    proof_assert!(a3@ == *a3_model);
    proof_assert!(a4@ == *a_model);
}
