//! A resource wrapping a [`FMap`] in a [`View`].
//!
//! This module defines a specialization of [`Resource`] for the case where you want:
//! - A single, authoritative version of a [`FMap`]
//! - Multiple fragments of such a map, that each assert that some key-value is in the
//!   map.
//!
//! These are the [`Authority`] and [`Fragment`] types respectively.

#[cfg(creusot)]
use crate::logic::{
    Id,
    ra::{Excl, RA as _},
};
use crate::{
    logic::{
        FMap,
        ra::{Ag, View, ViewRel},
    },
    resource::Resource,
    *,
};
use ::std::marker::PhantomData;

/// The relation used to relate an [`Authority`] with a [`Fragment`].
pub struct MapRelation<K, V>(PhantomData<(K, V)>);

impl<K, V> ViewRel for MapRelation<K, V> {
    type Auth = FMap<K, V>;
    type Frag = FMap<K, Ag<V>>;

    #[logic]
    #[open]
    fn rel(a: Self::Auth, f: Self::Frag) -> bool {
        f.valid()
            && pearlite! {
                forall<k: K> match f.get(k) {
                    Some(Ag::Ag(v)) => a.get(k) == Some(v),
                    _ => true,
                }
            }
    }

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1) != None)]
    #[ensures(Self::rel(a, f2))]
    #[open]
    fn rel_mono(a: Self::Auth, f1: Self::Frag, f2: Self::Frag) {
        match f2.incl(f1) {
            None => {}
            Some(_) => {
                proof_assert!(forall<k: K> match f2.get(k) {
                    Some(Ag::Ag(v)) => f1.get(k) == Some(Ag::Ag(v)),
                    _ => true,
                });
            }
        }
    }
}

/// Inner value for [`Resource`] and [`Fragment`].
type FMapView<K, V> = Resource<View<MapRelation<K, V>>>;

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// This is the authoritative version
pub struct Authority<K, V>(FMapView<K, V>);

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// This is the fragment version
pub struct Fragment<K, V>(FMapView<K, V>);

impl<K, V> Invariant for Authority<K, V> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.0@.auth != None && self.0@.frag == None }
    }
}
impl<K, V> Invariant for Fragment<K, V> {
    #[predicate]
    #[open(self)]
    fn invariant(self) -> bool {
        pearlite! { self.0@.auth == None && match self.0@.frag {
            Some(f) => f.len() == 1,
            None => false,
        } }
    }
}

impl<K, V> crate::View for Authority<K, V> {
    type ViewTy = FMap<K, V>;
    #[logic]
    #[open]
    fn view(self) -> FMap<K, V> {
        self.auth()
    }
}
impl<K, V> crate::View for Fragment<K, V> {
    type ViewTy = (K, V);
    #[logic]
    #[open]
    fn view(self) -> (K, V) {
        self.frag()
    }
}

impl<K, V> Authority<K, V> {
    /// Id of the underlying [`Resource`].
    #[logic]
    #[open(self)]
    pub fn id(self) -> Id {
        self.0.id()
    }

    /// Get the authoritative version of the map.
    ///
    /// This can also be accessed using the [`view`](crate::View::view) operator `@`.
    #[logic]
    #[open(self)]
    pub fn auth(self) -> FMap<K, V> {
        match self.0.val().auth {
            None => FMap::empty(),
            Some(Excl::Bot) => FMap::empty(),
            Some(Excl::Excl(auth)) => auth,
        }
    }

    /// Create a new, empty authoritative map.
    #[ensures(result@ == FMap::empty())]
    pub fn new() -> Ghost<Self> {
        let resource = Resource::alloc(snapshot!(View::mkauth(FMap::empty())));
        ghost!(Self(resource.into_inner()))
    }

    /// Insert a new element in the authoritative map and return the corresponding
    /// fragment.
    #[requires(!self@.contains(*k))]
    #[ensures((^self)@ == self@.insert(*k, *v))]
    #[ensures((^self).id() == self.id())]
    #[ensures(result@ == (*k, *v))]
    #[ensures(result.id() == self.id())]
    #[pure]
    #[allow(unused_variables)]
    pub fn insert(&mut self, k: Snapshot<K>, v: Snapshot<V>) -> Fragment<K, V> {
        let new_auth = snapshot!(View::mkauth(self.auth().insert(*k, *v)));
        self.0.update(new_auth);
        let right = snapshot!(self.0@);
        let left = snapshot!(View::mkfrag(FMap::empty().insert(*k, Ag::Ag(*v))));
        Fragment(self.0.split_off(right, left))
    }

    /// Asserts that the fragment represented by `frag` is contained in `self`.
    #[requires(self.id() == frag.id())]
    #[ensures(self.auth().get(frag@.0) == Some(frag@.1))]
    #[pure]
    #[allow(unused_variables)]
    pub fn contains(&self, frag: &Fragment<K, V>) {
        let new_resource = self.0.join_shared(&frag.0);
        proof_assert!(frag.0@.incl(new_resource@) != None);
    }
}

impl<K, V> Fragment<K, V> {
    /// Id of the underlying [`Resource`].
    #[logic]
    #[open(self)]
    pub fn id(self) -> Id {
        self.0.id()
    }

    /// Get the fragment of the map represented by this resource.
    ///
    /// This can also be accessed using the [`view`](crate::View::view) operator `@`.
    #[logic]
    #[open(self)]
    pub fn frag(self) -> (K, V) {
        let frag_agree = match self.0.val().frag {
            None => FMap::empty(),
            Some(frag) => frag,
        };
        such_that(|(k, v)| frag_agree.get(k) == Some(Ag::Ag(v)))
    }
}

impl<K, V> Clone for Fragment<K, V> {
    #[pure]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}
