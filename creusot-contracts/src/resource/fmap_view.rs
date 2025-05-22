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

struct MapRelation<K, V>(PhantomData<(K, V)>);

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
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    #[open]
    fn rel_mono(a: Self::Auth, f1: Self::Frag, f2: Self::Frag) {}
}

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// One of the `FMapView` will be the _authoritative_ version: it is unique and nonduplicable.
///
/// Then, one may obtain _fragments_ of this authoritative version, asserting that some
/// `(key, value)` pairs are indeed in the map.
pub struct FMapView<K, V>(Resource<View<MapRelation<K, V>>>);

impl<K, V> FMapView<K, V> {
    /// Id of the underlying [`Resource`].
    #[logic]
    #[open(self)]
    pub fn id(self) -> Id {
        self.0.id()
    }

    /// True if this is the authoritative version of the map.
    ///
    /// Use [`Self::auth`] to get the actual authoritative version.
    #[predicate]
    #[open(self)]
    pub fn is_auth(self) -> bool {
        self.0.val().auth != None
    }

    /// True if this is a fragment of the map.
    ///
    /// This is _not_ incompatible with [`Self::is_auth`].
    ///
    /// Use [`Self::frag`] to get the actual fragment version.
    #[predicate]
    #[open(self)]
    pub fn is_frag(self) -> bool {
        self.0.val().frag != None
    }

    /// Get the authoritative version of the map, or the empty map.
    #[logic]
    #[open(self)]
    pub fn auth(self) -> FMap<K, V> {
        match self.0.val().auth {
            None => FMap::empty(),
            Some(Excl::Bot) => FMap::empty(),
            Some(Excl::Excl(auth)) => auth,
        }
    }

    #[logic]
    #[open(self)]
    fn frag_agree(self) -> FMap<K, Ag<V>> {
        match self.0.val().frag {
            None => FMap::empty(),
            Some(frag) => frag,
        }
    }

    /// Get the fragment version of the map, or the empty map.
    #[logic]
    #[open(self)]
    pub fn frag(self) -> FMap<K, V> {
        self.frag_agree().filter_map(|(_, v)| match v {
            Ag::Ag(v) => Some(v),
            Ag::Bot => None,
        })
    }
}

impl<K, V> FMapView<K, V> {
    /// Create a new, empty authoritative map.
    #[ensures(result.is_auth())]
    #[ensures(!result.is_frag())]
    #[ensures(result.auth() == FMap::empty())]
    pub fn new() -> Ghost<Self> {
        let resource = Resource::alloc(snapshot!(View::mkauth(FMap::empty())));
        ghost!(Self(resource.into_inner()))
    }

    /// If we have the authoritative version, insert a new element and return the
    /// corresponding fragment.
    #[requires(self.is_auth() && !self.auth().contains(*k))]
    #[ensures((^self).is_auth() && (^self).auth() == self.auth().insert(*k, *v))]
    #[ensures((^self).is_frag() == self.is_frag() && (^self).frag() == self.frag())]
    #[ensures((^self).id() == self.id())]
    #[ensures(!result.is_auth() && result.is_frag())]
    #[ensures(result.frag() == FMap::empty().insert(*k, *v))]
    #[ensures(result.id() == self.id())]
    #[pure]
    #[allow(unused_variables)]
    pub fn insert(&mut self, k: Snapshot<K>, v: Snapshot<V>) -> Self {
        let new_auth = snapshot!(View::mkauth(self.auth().insert(*k, *v)));
        let new_total = snapshot!(match self.0@.frag {
            None => *new_auth,
            Some(frag) => new_auth.op(View::mkfrag(frag)),
        });
        self.0.update(new_total);
        let right = snapshot!(self.0@);
        let left = snapshot!(View::mkfrag(FMap::empty().insert(*k, Ag::Ag(*v))));
        Self(self.0.split_off(right, left))
    }

    /// Asserts that the fragment part of `frag` is contained in the authoritative
    /// part of `self` (if both exist).
    #[requires(self.id() == frag.id())]
    #[requires(self.is_auth() && frag.is_frag())]
    #[ensures(forall<k: _> match frag.frag().get(k) {
            Some(v) => self.auth().get(k) == Some(v),
            _ => true,
        })]
    #[pure]
    #[allow(unused_variables)]
    pub fn contains(&self, frag: &Self) {
        let new_resource = self.0.join_shared(&frag.0);
        let new_frag = snapshot!(match new_resource@.frag {
            None => FMap::empty(),
            Some(map) => map,
        });
        let old_frag = snapshot!(match frag.0@.frag {
            None => FMap::empty(),
            Some(map) => map,
        });
        proof_assert!(forall<k: _> match frag.frag().get(k) {
            Some(v) => new_frag.get(k) == Some(Ag::Ag(v)),
            None => true,
        });
    }
}
