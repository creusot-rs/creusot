use crate::{
    logic::ra::{
        RA,
        view::{View, ViewRel},
    },
    *,
};

// TODO: open vs open(self) for RA impls? abstraction patterns?

pub struct AuthViewRel<T>(T);

impl<T> ViewRel for AuthViewRel<T>
where
    T: RA,
{
    type Auth = T;
    type Frac = T;

    #[logic]
    #[open]
    fn rel(a: Self::Auth, f: Self::Frac) -> bool {
        f.incl(a) && a.valid()
    }

    #[law]
    #[open(self)]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frac, f2: Self::Frac) {}
}

/// The 'authority' Resource Algebra.
///
/// This is a specialisation of [`View`], where:
/// - both `Auth` and `Frac` are the same type
/// - the relation between the two is that `Frac` must always be included in `Auth`
pub struct Auth<T: RA>(pub View<AuthViewRel<T>>);

impl<T> Auth<T>
where
    T: RA,
{
    /// Create a new `Auth` containing an authoritative version of `x`.
    #[logic]
    #[open]
    pub fn mkauth(x: T) -> Self {
        Auth(View::mkauth(x))
    }

    /// Create a new `Auth` containing a fractional version of `x`.
    #[logic]
    #[open]
    pub fn mkfrac(x: T) -> Self {
        Auth(View::mkfrac(x))
    }
}

impl<T> RA for Auth<T>
where
    T: RA,
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        Auth(self.0.op(other.0))
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        self.0.valid()
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
        self.0.valid_op(b.0)
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
        self.0.maximal_idemp();
    }

    #[logic]
    #[open]
    #[ensures(result == exists<c: Self> self.op(c) == other)]
    fn incl(self, other: Self) -> bool {
        self.0.incl(other.0)
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        self.0.idemp()
    }
}
