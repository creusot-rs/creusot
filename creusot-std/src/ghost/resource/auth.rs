use super::Resource;
use crate::{
    logic::{
        Id,
        ra::{
            UnitRA,
            auth::{Auth, AuthIncrease, AuthUpdate},
            update::LocalUpdate,
        },
    },
    prelude::*,
};

/// Wrapper around a [`Resource`], that contains an authoritative value.
///
/// This type is a specialization of [`Resource`] for the common case where you want an
/// authoritative resource. [`Authority`] and [`Fragment`] respectively contain the
/// authoritative part and the fragment part of the ressource, and come with handy ghost
/// functions to use them (provers have some trouble authomatically deriving when the
/// context is full of other hypotheses).
pub struct Authority<R: UnitRA>(Resource<Auth<R>>);

/// Wrapper around a [`Resource`], that contains a fragment.
///
/// See [`Authority`].
pub struct Fragment<R: UnitRA>(pub Resource<Auth<R>>);

impl<R: UnitRA> Invariant for Authority<R> {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.0@.auth() != None }
    }
}

impl<R: UnitRA> View for Authority<R> {
    type ViewTy = R;

    /// Get the authoritative value.
    #[logic]
    fn view(self) -> R {
        self.0.view().auth().unwrap_logic()
    }
}

impl<R: UnitRA> View for Fragment<R> {
    type ViewTy = R;

    /// Get the fragment value.
    #[logic(open)]
    fn view(self) -> R {
        pearlite! { self.0@.frag() }
    }
}

impl<R: UnitRA> From<Resource<Auth<R>>> for Fragment<R> {
    #[check(ghost)]
    #[ensures(result@ == value@.frag())]
    fn from(value: Resource<Auth<R>>) -> Self {
        Fragment(value)
    }
}

impl<R: UnitRA> Authority<R> {
    /// Id of the underlying [`Resource`].
    #[logic]
    pub fn id(self) -> Id {
        self.0.id()
    }

    /// Get the id for this resource.
    ///
    /// This is the same as [`Self::id`], but for ghost code.
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self.id())]
    pub fn id_ghost(&self) -> Id {
        self.0.id_ghost()
    }

    /// Create a new, empty authority.
    #[check(ghost)]
    #[ensures(result@ == R::unit())]
    #[allow(unused_variables)]
    pub fn alloc() -> Ghost<Self> {
        ghost!(Self(Resource::alloc(snapshot!(Auth::new_auth(R::unit()))).into_inner()))
    }

    /// Create a new authority/fragment pair from a raw [`Auth`] resource.
    #[check(ghost)]
    #[requires(r@.auth() != None)]
    #[ensures(result.0.id() == r.id() && result.1.id() == r.id())]
    #[ensures(result.0@ == r@.auth().unwrap_logic())]
    #[ensures(result.1@ == r@.frag())]
    pub fn from_resource(mut r: Resource<Auth<R>>) -> (Self, Fragment<R>) {
        let fragment = snapshot!(Auth::new_frag(r@.frag()));
        let authority = snapshot!(Auth::new_auth(r@.auth().unwrap_logic()));
        let frag = r.split_off(fragment, authority);
        (Self(r), Fragment(frag))
    }

    /// Perform a local update on an authority, fragment pair
    #[check(ghost)]
    #[requires(self.id() == frag.id())]
    #[requires(upd.premise(self@, frag@))]
    #[ensures(self.id() == (^self).id())]
    #[ensures(frag.id() == (^frag).id())]
    #[ensures(frag@.incl(self@))]
    #[ensures(((^self)@, (^frag)@) == upd.update(self@, frag@))]
    #[allow(unused_variables)]
    pub fn update<U: LocalUpdate<R>>(&mut self, frag: &mut Fragment<R>, upd: U) {
        let from = snapshot!(Auth::new(Some(self@), frag@));
        self.0.join_in(frag.0.take());
        // Discard the spurious frag part of the auth
        self.0.weaken(from);
        self.0.update(AuthUpdate(upd));
        let rs = snapshot!((Auth::new_frag(self.0@.frag()), Auth::new(self.0@.auth(), R::unit())));
        frag.0 = self.0.split_off(snapshot!(rs.0), snapshot!(rs.1));
    }

    /// Add a piece to the authority, and return a new fragment corresponding to this piece.
    #[check(ghost)]
    #[requires(self@.op(*frag) != None)]
    #[ensures((^self)@ == self@.op(*frag).unwrap_logic())]
    #[ensures(result@ == *frag)]
    #[ensures(result.id() == self.id() && (^self).id() == self.id())]
    #[allow(unused_variables)]
    pub fn add_fragment(&mut self, frag: Snapshot<R>) -> Fragment<R> {
        let mut unit: Fragment<R> = Fragment::new_unit(self.id_ghost());
        self.update(&mut unit, AuthIncrease(frag));
        unit
    }

    /// Asserts that the fragment represented by `frag` is contained in `self`.
    #[check(ghost)]
    #[requires(self.id() == frag.id())]
    #[ensures(frag@.incl(self@))]
    pub fn frag_lemma(&self, frag: &Fragment<R>) {
        self.0.join_shared(&frag.0);
    }
}

impl<R: UnitRA> Fragment<R> {
    /// Id of the underlying [`Resource`].
    #[logic]
    pub fn id(self) -> Id {
        self.0.id()
    }

    /// Get the id for this resource.
    ///
    /// This is the same as [`Self::id`], but for ghost code.
    #[trusted]
    #[check(ghost)]
    #[ensures(result == self.id())]
    pub fn id_ghost(&self) -> Id {
        self.0.id_ghost()
    }

    /// Create a fragment containing a unit resource
    #[check(ghost)]
    #[ensures(result@ == R::unit() && result.id() == id)]
    pub fn new_unit(id: Id) -> Fragment<R> {
        Fragment(Resource::new_unit(id))
    }

    /// Duplicate the duplicable core of a fragment
    #[check(ghost)]
    #[ensures(result.id() == self.id())]
    #[ensures(result@ == self@.core_total())]
    pub fn core(&self) -> Self {
        Fragment(self.0.core())
    }

    /// Split a fragment into two parts, described by `a` and `b`.
    ///
    /// See also [`Self::split_off`].
    #[check(ghost)]
    #[requires(R::incl_eq_op(*a, *b, self@))]
    #[ensures(result.0.id() == self.id() && result.1.id() == self.id())]
    #[ensures(result.0@ == *a)]
    #[ensures(result.1@ == *b)]
    #[allow(unused_variables)]
    pub fn split(self, a: Snapshot<R>, b: Snapshot<R>) -> (Self, Self) {
        let (r1, r2) = self.0.split(snapshot!(Auth::new_frag(*a)), snapshot!(Auth::new_frag(*b)));
        (Fragment(r1), Fragment(r2))
    }

    /// Remove `r` from `self` and return it, leaving `s` in `self`.
    #[check(ghost)]
    #[requires(R::incl_eq_op(*r, *s, self@))]
    #[ensures((^self).id() == self.id() && result.id() == self.id())]
    #[ensures((^self)@ == *s)]
    #[ensures(result@ == *r)]
    #[allow(unused_variables)]
    pub fn split_off(&mut self, r: Snapshot<R>, s: Snapshot<R>) -> Self {
        Fragment(self.0.split_off(snapshot!(Auth::new_frag(*r)), snapshot!(Auth::new_frag(*s))))
    }

    /// Join two owned framents together.
    ///
    /// See also [`Self::join_in`] and [`Self::join_shared`].
    #[check(ghost)]
    #[requires(self.id() == other.id())]
    #[ensures(result.id() == self.id())]
    #[ensures(Some(result@) == self@.op(other@))]
    pub fn join(self, other: Self) -> Self {
        Fragment(self.0.join(other.0))
    }

    /// Same as [`Self::join`], but put the result into `self`.
    #[check(ghost)]
    #[requires(self.id() == other.id())]
    #[ensures((^self).id() == self.id())]
    #[ensures(Some((^self)@) == self@.op(other@))]
    pub fn join_in(&mut self, other: Self) {
        self.0.join_in(other.0)
    }

    /// Transforms `self` into `target`, given that `target` is included in `self`.
    #[check(ghost)]
    #[requires(target.incl(self@))]
    #[ensures((^self).id() == self.id())]
    #[ensures((^self)@ == *target)]
    #[allow(unused_variables)]
    pub fn weaken(&mut self, target: Snapshot<R>) {
        self.0.weaken(snapshot! { Auth::new_frag(*target) });
    }

    /// Validate the composition of `self` and `other`.
    #[check(ghost)]
    #[requires(self.id() == other.id())]
    #[ensures(^self == *self)]
    #[ensures(self@.op(other@) != None)]
    pub fn valid_op_lemma(&mut self, other: &Self) {
        self.0.valid_op_lemma(&other.0);
    }
}
