//! A resource wrapping a [`FMap`] in a [`View`].
//!
//! This module defines a specialization of [`Resource`] for the case where you want:
//! - A single, authoritative version of a [`FMap`]
//! - Multiple fragments of such a map, that each assert that some key-value is in the
//!   map.
//!
//! These are the [`Authority`] and [`Fragment`] types respectively.

#[cfg(creusot)]
use crate::logic::Id;
use crate::{
    logic::{
        FMap,
        ra::{
            agree::Ag,
            auth::{Auth, AuthUpdate},
            fmap::FMapInsertLocalUpdate,
        },
    },
    resource::Resource,
    *,
};

/// Inner value for [`Resource`] and [`Fragment`].
type FMapAuth<K, V> = Resource<Auth<FMap<K, Ag<V>>>>;

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// This is the authoritative version
pub struct Authority<K, V>(FMapAuth<K, V>);

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// This is the fragment version
pub struct Fragment<K, V>(FMapAuth<K, V>, Snapshot<K>, Snapshot<V>);

impl<K, V> Invariant for Authority<K, V> {
    #[logic]
    fn invariant(self) -> bool {
        self.0.view().auth() != None
    }
}
impl<K, V> Invariant for Fragment<K, V> {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.0@.frag().get(*self.1) == Some(Ag(*self.2)) }
    }
}

impl<K, V> crate::View for Authority<K, V> {
    type ViewTy = FMap<K, V>;

    /// Get the authoritative version of the map.
    #[logic]
    fn view(self) -> FMap<K, V> {
        self.0.view().auth().unwrap_logic().map(|(_, x): (K, Ag<V>)| x.0)
    }
}
impl<K, V> crate::View for Fragment<K, V> {
    type ViewTy = (K, V);

    /// Get the fragment of the map represented by this resource.
    #[logic]
    fn view(self) -> (K, V) {
        (*self.1, *self.2)
    }
}

impl<K, V> Authority<K, V> {
    /// Id of the underlying [`Resource`].
    #[logic]
    pub fn id(self) -> Id {
        self.0.id()
    }

    /// Create a new, empty authoritative map.
    #[check(ghost)]
    #[ensures(result@ == FMap::empty())]
    pub fn new() -> Ghost<Self> {
        let r =
            ghost!(Self(Resource::alloc(snapshot!(Auth::new_auth(FMap::empty()))).into_inner()));
        proof_assert!(r@.ext_eq(FMap::empty()));
        r
    }

    /// Insert a new element in the authoritative map and return the corresponding
    /// fragment.
    #[requires(!self@.contains(*k))]
    #[ensures((^self)@ == self@.insert(*k, *v))]
    #[ensures((^self).id() == self.id())]
    #[ensures(result@ == (*k, *v))]
    #[ensures(result.id() == self.id())]
    #[check(ghost)]
    #[allow(unused_variables)]
    pub fn insert(&mut self, k: Snapshot<K>, v: Snapshot<V>) -> Fragment<K, V> {
        let s = snapshot!(*self);
        self.0.update(AuthUpdate(FMapInsertLocalUpdate(k, snapshot!(Ag(*v)))));
        proof_assert!(self@.ext_eq(s@.insert(*k, *v)));
        Fragment(self.0.core(), k, v)
    }

    /// Asserts that the fragment represented by `frag` is contained in `self`.
    #[requires(self.id() == frag.id())]
    #[ensures(self@.get(frag@.0) == Some(frag@.1))]
    #[check(ghost)]
    #[allow(unused_variables)]
    pub fn contains(&self, frag: &Fragment<K, V>) {
        let new_resource = self.0.join_shared(&frag.0);
        proof_assert!(new_resource@.frag().get(frag@.0) == Some(Ag(frag@.1)));
    }
}
impl<K, V> Fragment<K, V> {
    /// Id of the underlying [`Resource`].
    #[logic]
    pub fn id(self) -> Id {
        self.0.id()
    }
}

impl<K, V> Clone for Fragment<K, V> {
    #[check(ghost)]
    #[ensures(result@ == self@)]
    fn clone(&self) -> Self {
        Self(self.0.core(), self.1, self.2)
    }
}
