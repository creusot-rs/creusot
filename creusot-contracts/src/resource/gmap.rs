#[cfg(creusot)]
use crate::logic::ra::{Excl, RA as _};
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
    type Frac = FMap<K, Ag<V>>;

    #[logic]
    #[open]
    fn rel(a: Self::Auth, f: Self::Frac) -> bool {
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
    fn rel_mono(a: Self::Auth, f1: Self::Frac, f2: Self::Frac) {}
}

/// Wrapper around a [`Resource`], that allows to agree on the values of the map.
///
/// One of the GMap will be the _authoritative_ version: it is unique and nonduplicable.
///
/// Then, one may obtain _fragments_ of this authoritative version, asserting that some
/// `(key, value)` pairs are indeed in the map.
pub struct GMap<K, V>(Resource<View<MapRelation<K, V>>>);

impl<K, V> GMap<K, V> {
    /// Id of the underlying [`Resource`].
    #[logic]
    #[open(self)]
    pub fn id(self) -> pcell::Id {
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
    /// Use [`Self::frac`] to get the actual fragment version.
    #[predicate]
    #[open(self)]
    pub fn is_frac(self) -> bool {
        self.0.val().frac != None
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
    fn frac_agree(self) -> FMap<K, Ag<V>> {
        match self.0.val().frac {
            None => FMap::empty(),
            Some(frac) => frac,
        }
    }

    /// Get the fraction version of the map, or the empty map.
    #[logic]
    #[open(self)]
    pub fn frac(self) -> FMap<K, V> {
        self.frac_agree().map_filter(|v| match v {
            Ag::Ag(v) => Some(v),
            Ag::Bot => None,
        })
    }
}

impl<K, V> GMap<K, V> {
    /// Create a new, empty authoritative map.
    #[ensures(result.is_auth())]
    #[ensures(!result.is_frac())]
    #[ensures(result.auth() == FMap::empty())]
    pub fn new() -> Ghost<Self> {
        let resource = Resource::alloc(snapshot!(View::mkauth(FMap::empty())));
        ghost!(Self(resource.into_inner()))
    }

    /// If we have the authoritative version, insert a new element and return the
    /// corresponding fraction.
    #[requires(self.is_auth() && !self.auth().contains(*k))]
    #[ensures((^self).is_auth() && (^self).auth() == self.auth().insert(*k, *v))]
    #[ensures((^self).is_frac() == self.is_frac() && (^self).frac() == self.frac())]
    #[ensures((^self).id() == self.id())]
    #[ensures(!result.is_auth() && result.is_frac())]
    #[ensures(result.frac() == FMap::empty().insert(*k, *v))]
    #[ensures(result.id() == self.id())]
    #[pure]
    #[allow(unused_variables)]
    pub fn insert(&mut self, k: Snapshot<K>, v: Snapshot<V>) -> Self {
        let new_auth = snapshot!(View::mkauth(self.auth().insert(*k, *v)));
        let new_total = snapshot!(match self.0@.frac {
            None => *new_auth,
            Some(frac) => new_auth.op(View::mkfrac(frac)),
        });
        self.0.update(new_total);
        let right = snapshot!(self.0@);
        let left = snapshot!(View::mkfrac(FMap::empty().insert(*k, Ag::Ag(*v))));
        Self(self.0.split_off(right, left))
    }

    /// Asserts that the fractional part of `frac` is contained in the authoritative
    /// part of `self` (if both exist).
    #[requires(self.id() == frac.id())]
    #[requires(self.is_auth() && frac.is_frac())]
    #[ensures(forall<k: _> match frac.frac().get(k) {
            Some(v) => self.auth().get(k) == Some(v),
            _ => true,
        })]
    #[pure]
    #[allow(unused_variables)]
    pub fn contains(&self, frac: &Self) {
        let new_resource = self.0.join_shared(&frac.0);
        let new_frac = snapshot!(match new_resource@.frac {
            None => FMap::empty(),
            Some(map) => map,
        });
        let old_frac = snapshot!(match frac.0@.frac {
            None => FMap::empty(),
            Some(map) => map,
        });
        proof_assert!(old_frac.incl(*new_frac));
        proof_assert!(forall<k: _> match frac.frac().get(k) {
            Some(v) => new_frac.get(k) == Some(Ag::Ag(v)),
            None => true,
        });
    }
}
