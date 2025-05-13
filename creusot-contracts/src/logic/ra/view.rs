use crate::*;
use crate::logic::ra::{RA, excl::{Excl, Excl::*}};

pub trait ViewRel {
    type Auth;
    type Frac: RA;

    #[logic]
    fn rel(a: Self::Auth, f: Self::Frac) -> bool;

    #[law]
    #[requires(Self::rel(a, f1))]
    #[requires(f2.incl(f1))]
    #[ensures(Self::rel(a, f2))]
    fn rel_mono(a: Self::Auth, f1: Self::Frac, f2: Self::Frac);
}

// NOTE: we could add (discardable) fractions for the auth part
#[allow(dead_code)]
pub struct View<R> where R: ViewRel
{
    // TODO: should the fields be priv?
    pub auth: Option<Excl<R::Auth>>,
    pub frac: Option<R::Frac>,
}

impl<R> View<R> where R: ViewRel {
    #[logic]
    #[open]
    pub fn mkauth(a: R::Auth) -> Self {
        Self { auth: Some(Excl(a)), frac: None }
    }

    #[logic]
    #[open]
    pub fn mkfrac(f: R::Frac) -> Self {
        Self { auth: None, frac: Some(f) }
    }
}

impl<R> RA for View<R>
where R: ViewRel
{
    #[logic]
    #[open]
    fn op(self, other: Self) -> Self {
        let (auth, frac) = (self.auth, self.frac).op((other.auth, other.frac));
        Self { auth, frac }
    }

    #[logic]
    #[open]
    fn valid(self) -> bool { pearlite!{
        match self {
            Self { auth: Some(Excl(a)), frac: Some(f) } => f.valid() && R::rel(a, f),
            // TODO: why is this condition necessary?
            Self { auth: None, frac: Some(f) } => f.valid() && exists<a: R::Auth> R::rel(a, f),
            Self { auth: Some(Excl(_)), frac: None } => true,
            Self { auth: None, frac: None } => true,
            Self { auth: Some(ExclBot), frac: _ } => false,
        }
    }}

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        (self.auth, self.frac).incl((other.auth, other.frac))
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        (self.auth, self.frac).idemp()
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) { }

    #[law]
    #[open(self)]
    #[ensures(a.op(b).op(c) == a.op(b.op(c)))]
    fn associative(a: Self, b: Self, c: Self) { }

    #[logic]
    #[open(self)]
    #[ensures(self.op(b).valid() ==> self.valid())]
    fn valid_op(self, b: Self) {
        let _ = <R::Frac as RA>::valid_op;
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
        self.frac.maximal_idemp();
    }
}
