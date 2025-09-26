// This is an other implementation of fmap_view, but using the View RA directly instead of Auth.

extern crate creusot_contracts;
use ::std::marker::PhantomData;
use creusot_contracts::{
    ghost::resource::Resource,
    logic::{
        FMap, Id,
        ra::{
            RA, UnitRA,
            agree::Ag,
            view::{View as ViewRA, ViewRel, ViewUpdateInsert},
        },
    },
    *,
};

/// The relation used to relate an [`Authority`] with a [`Fragment`].
pub struct MapRelation<K, V>(PhantomData<(K, V)>);

impl<K, V> ViewRel for MapRelation<K, V> {
    type Auth = FMap<K, V>;
    type Frag = FMap<K, Ag<V>>;

    #[logic(open)]
    fn rel(a: Option<Self::Auth>, f: Self::Frag) -> bool {
        pearlite! {
            match a {
                Some(a) => forall<k: K> match f.get(k) {
                    Some(Ag(v)) => a.get(k) == Some(v),
                    _ => true,
                },
                None => true
            }
        }
    }

    #[logic(law)]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Option<Self::Auth>, f1: Self::Frag, f2: Self::Frag) {}

    #[logic(law)]
    #[requires(Self::rel(a, f))]
    #[ensures(Self::rel(None, f))]
    fn rel_none(a: Option<Self::Auth>, f: Self::Frag) {}

    #[logic(law)]
    #[ensures(Self::rel(a, Self::Frag::unit()))]
    fn rel_unit(a: Option<Self::Auth>) {}
}

/// Inner value for [`Resource`] and [`Fragment`].
type FMapView<K, V> = Resource<ViewRA<MapRelation<K, V>>>;

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// This is the authoritative version
pub struct Authority<K, V>(FMapView<K, V>);

/// Wrapper around a [`Resource`], that allows to agree on the values of a [`FMap`].
///
/// This is the fragment version
pub struct Fragment<K, V>(FMapView<K, V>, Snapshot<K>, Snapshot<V>);

impl<K, V> Invariant for Authority<K, V> {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.0@.auth() != None }
    }
}
impl<K, V> Invariant for Fragment<K, V> {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! {
            ViewRA::new_frag(FMap::singleton(*self.1, Ag(*self.2))).incl(self.0@)
        }
    }
}

impl<K, V> View for Authority<K, V> {
    type ViewTy = FMap<K, V>;

    /// Get the authoritative version of the map.
    #[logic]
    fn view(self) -> FMap<K, V> {
        pearlite! { self.0@.auth().unwrap_logic() }
    }
}
impl<K, V> View for Fragment<K, V> {
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
        let resource = Resource::alloc(snapshot!(ViewRA::new_auth(FMap::empty())));
        ghost!(Self(resource.into_inner()))
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
        let auth = snapshot!(self@.insert(*k, *v));
        let frag = snapshot!(FMap::singleton(*k, Ag(*v)));
        self.0.update(ViewUpdateInsert(auth, frag));
        Fragment(
            self.0
                .split_off(snapshot!(ViewRA::new_frag(*frag)), snapshot!(ViewRA::new_auth(*auth))),
            snapshot!(*k),
            snapshot!(*v),
        )
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
