use crate::{
    logic::ra::{RA, excl::Excl},
    *,
};

/// The relation used in [`View`].
pub trait ViewRel {
    /// The type of the _authority_ portion of a view
    type Auth;
    /// The type of a _fragment_ portion of a view
    type Frag: RA;

    /// The relation between the authority and a fragment
    #[logic]
    fn rel(a: Self::Auth, f: Self::Frag) -> bool;

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frag, f2: Self::Frag);
}

/// The 'view' Resource Algebra.
///
/// This resource is parametrized by a [relation](ViewRel) `R` between an
/// **authoritative** part (of type `R::Auth`) and a **fragment** part
/// (of type `R::Frag`).
///
/// The authoritative part is unique, while the fragment part might not be. When the
/// two are present, the relation between the two must hold in order for the view to
/// be [valid](RA::valid).
// NOTE: we could add (discardable) fragments for the auth part
pub struct View<R>
where
    R: ViewRel,
{
    /// Authoritative part of the view
    ///
    /// Note the [`Excl`], which guarantees that only one [`Resource`] wrapping a
    /// [`View`] may have the authority part.
    pub auth: Option<Excl<R::Auth>>,
    /// Fragment part of the view
    pub frag: Option<R::Frag>,
}

impl<R> View<R>
where
    R: ViewRel,
{
    /// Create a new `View` containing an authoritative version of `x`.
    #[logic]
    #[open]
    pub fn mkauth(a: R::Auth) -> Self {
        Self { auth: Some(Excl::Excl(a)), frag: None }
    }

    /// Create a new `View` containing a fragment version of `x`.
    #[logic]
    #[open]
    pub fn mkfrag(f: R::Frag) -> Self {
        Self { auth: None, frag: Some(f) }
    }
}

impl<R> RA for View<R>
where
    R: ViewRel,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        let (auth, frag) = (self.auth, self.frag).op((other.auth, other.frag));
        Self { auth, frag }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        pearlite! {
            match self {
                Self { auth: Some(Excl::Excl(a)), frag: Some(f) } => f.valid() && R::rel(a, f),
                // TODO: why is this condition necessary? Try to remove it
                Self { auth: None, frag: Some(f) } => f.valid() && exists<a: R::Auth> R::rel(a, f),
                Self { auth: Some(Excl::Excl(_)), frag: None } => true,
                Self { auth: None, frag: None } => true,
                Self { auth: Some(Excl::Bot), frag: _ } => false,
            }
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        (self.auth, self.frag).incl((other.auth, other.frag))
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        (self.auth, self.frag).idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <R::Frag as RA>::valid_op;
    }

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {
        self.auth.maximal_idemp();
        self.frag.maximal_idemp();
    }
}
