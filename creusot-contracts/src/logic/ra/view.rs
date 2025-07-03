use crate::{
    logic::{
        Mapping,
        ra::{RA, UnitRA, update::Update},
    },
    *,
};

/// The relation used in [`View`].
pub trait ViewRel {
    /// The type of the _authority_ portion of a view
    type Auth;
    /// The type of a _fragment_ portion of a view
    type Frag: UnitRA;

    /// The relation between the authority and a fragment
    #[logic]
    fn rel(a: Option<Self::Auth>, f: Self::Frag) -> bool;

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Option<Self::Auth>, f1: Self::Frag, f2: Self::Frag);

    #[law]
    #[requires(Self::rel(a, f))]
    #[ensures(Self::rel(None, f))]
    fn rel_none(a: Option<Self::Auth>, f: Self::Frag);

    #[law]
    #[ensures(Self::rel(a, Self::Frag::unit()))]
    fn rel_unit(a: Option<Self::Auth>);
}

/// The 'view' Resource Algebra.
///
/// This resource is parametrized by a [relation](ViewRel) `R` between an
/// **authoritative** part (of type `R::Auth`) and a **fragment** part
/// (of type `R::Frag`).
///
/// The authoritative part is unique, while the fragment part might not be. A relation
/// must hold between the two pasts.
// NOTE: we could add (discardable) fragments for the auth part
#[cfg_attr(not(creusot), allow(unused))]
struct InnerView<R: ViewRel> {
    /// Authoritative part of the view
    auth: Option<R::Auth>,
    /// Fragment part of the view
    frag: R::Frag,
}

impl<R: ViewRel> Invariant for InnerView<R> {
    #[logic]
    fn invariant(self) -> bool {
        R::rel(self.auth, self.frag)
    }
}

impl<R: ViewRel> InhabitedInvariant for InnerView<R> {
    #[logic]
    #[ensures(result.invariant())]
    fn inhabits() -> Self {
        Self { auth: None, frag: R::Frag::unit() }
    }
}

pub struct View<R: ViewRel>(Subset<InnerView<R>>);

impl<R: ViewRel> View<R> {
    /// Returns the authoritative part of a given `View`
    #[logic]
    pub fn auth(self) -> Option<R::Auth> {
        pearlite! { self.0@.auth }
    }

    #[logic]
    #[ensures(R::rel(self.auth(), result))]
    pub fn frag(self) -> R::Frag {
        pearlite! { self.0@.frag }
    }

    #[logic]
    #[open]
    #[ensures(result == (self == other))]
    pub fn ext_eq(self, other: Self) -> bool {
        let _ = Subset::<InnerView<R>>::view_inj;
        self.auth() == other.auth() && self.frag() == other.frag()
    }

    /// Create a new `View` with given authority and fragment.
    #[logic]
    #[requires(R::rel(auth, frag))]
    #[ensures(result.auth() == auth)]
    #[ensures(result.frag() == frag)]
    pub fn new(auth: Option<R::Auth>, frag: R::Frag) -> Self {
        Self(Subset::new_logic(InnerView { auth, frag }))
    }

    /// Create a new `View` containing an authoritative version of `x`.
    #[logic]
    #[open]
    pub fn new_auth(auth: R::Auth) -> Self {
        Self::new(Some(auth), R::Frag::unit())
    }

    /// Create a new `View` containing a fragment version of `x`.
    #[logic]
    #[open]
    #[requires(R::rel(None, frag))]
    pub fn new_frag(frag: R::Frag) -> Self {
        Self::new(None, frag)
    }
}

impl<R: ViewRel> RA for View<R> {
    #[logic]
    #[open]
    fn op(self, other: Self) -> Option<Self> {
        pearlite! {
            match self.frag().op(other.frag()) {
                Some(f) => match (self.auth(), other.auth()) {
                    (None, a) => if R::rel(a, f) { Some(Self::new(a, f)) } else { None },
                    (a, None) => if R::rel(a, f) { Some(Self::new(a, f)) } else { None },
                    _ => None
                }
                None => None
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        let _ = Subset::<InnerView<R>>::view_inj;
        match self.frag().factor(factor.frag()) {
            Some(f) => match (self.auth(), factor.auth()) {
                (Some(a), None) => Some(Self::new(Some(a), f)),
                (a1, a2) => {
                    if a1 == a2 {
                        Some(Self::new_frag(f))
                    } else {
                        None
                    }
                }
            },
            None => None,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        let _ = Subset::<InnerView<R>>::view_inj;
        self.auth() == None && self.frag().idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {
        match (a.frag().op(b.frag()), b.frag().op(c.frag())) {
            (Some(fab), Some(fbc)) => match (fab.op(c.frag()), a.frag().op(fbc)) {
                (Some(_), Some(_)) => (),
                _ => (),
            },
            _ => (),
        }
        let _ = Subset::<InnerView<R>>::view_inj;
    }

    #[logic]
    #[open(self)]
    #[ensures(match result {
        Some(b) => b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b),
        None => forall<b: Self> ! (b.incl(self) && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        pearlite! {
            Some(Self::new_frag(self.frag().maximal_idemp_total()))
        }
    }
}

impl<R: ViewRel> UnitRA for View<R> {
    #[logic]
    #[ensures(forall<x: Self> x.op(result) == Some(x))]
    fn unit() -> Self {
        Self::new_frag(R::Frag::unit())
    }
}

pub struct ViewUpdate<R: ViewRel, Choice>(pub Snapshot<Mapping<Choice, (R::Auth, R::Frag)>>);

impl<R: ViewRel, Choice> Update<View<R>> for ViewUpdate<R, Choice> {
    type Choice = Choice;

    #[logic]
    #[open]
    fn premise(self, from: View<R>) -> bool {
        pearlite! {
            from.auth() != None &&
            forall<f: R::Frag>
                match from.frag().op(f) {
                    Some(ff) => R::rel(from.auth(), ff),
                    None => false
                } ==>
                exists<ch: Choice>
                    match self.0[ch].1.op(f) {
                        Some(ff) => R::rel(Some(self.0[ch].0), ff),
                        None => false
                    }
        }
    }

    #[logic]
    #[open]
    fn update(self, _: View<R>, ch: Choice) -> View<R> {
        View::new(Some(self.0[ch].0), self.0[ch].1)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: View<R>, frame: View<R>) -> Choice {
        such_that(|ch| self.update(from, ch).op(frame) != None)
    }
}

pub struct ViewUpdateInsert<R: ViewRel>(pub Snapshot<R::Auth>, pub Snapshot<R::Frag>);

impl<R: ViewRel> Update<View<R>> for ViewUpdateInsert<R> {
    type Choice = ();

    #[logic]
    #[open]
    fn premise(self, from: View<R>) -> bool {
        pearlite! {
            from.auth() != None &&
            forall<f: R::Frag> R::rel(from.auth(), f) ==>
                match self.1.op(f) {
                    Some(ff) => R::rel(Some(*self.0), ff),
                    None => false
                }
        }
    }

    #[logic]
    #[open]
    fn update(self, _: View<R>, _: ()) -> View<R> {
        View::new(Some(*self.0), *self.1)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: View<R>, frame: View<R>) {}
}

pub struct ViewUpdateRemove<R: ViewRel>(pub Snapshot<R::Auth>);

impl<R: ViewRel> Update<View<R>> for ViewUpdateRemove<R> {
    type Choice = ();

    #[logic]
    #[open]
    fn premise(self, from: View<R>) -> bool {
        pearlite! {
            from.auth() != None &&
            forall<f: R::Frag>
                match from.frag().op(f) {
                    Some(ff) => R::rel(from.auth(), ff),
                    None => false
                } ==>
                R::rel(Some(*self.0), f)
        }
    }

    #[logic]
    #[open]
    fn update(self, _: View<R>, _: ()) -> View<R> {
        View::new_auth(*self.0)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: View<R>, frame: View<R>) {}
}
