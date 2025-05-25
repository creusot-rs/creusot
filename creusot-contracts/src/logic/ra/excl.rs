use crate::{logic::ra::RA, *};

/// The 'exclusive' Resource Algebra.
///
/// Combining those resource with [`RA::op`] **never** yields valid elements.
/// As such, only one version of this resource (when using
/// [`Resource`](crate::resource::Resource)) will be able to exists at a given moment.
pub enum Excl<T> {
    Excl(T),
    /// The invalid value
    Bot,
}

impl<T> RA for Excl<T> {
    #[logic]
    #[open]
    fn op(self, _other: Self) -> Self {
        Self::Bot
    }

    #[logic]
    #[open]
    fn valid(self) -> bool {
        match self {
            Self::Excl(_) => true,
            Self::Bot => false,
        }
    }

    #[logic]
    #[open]
    #[ensures(result == (exists<c: Self> self.op(c) == other))]
    fn incl(self, other: Self) -> bool {
        other == Self::Bot
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == self))]
    fn idemp(self) -> bool {
        self == Self::Bot
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
    fn valid_op(self, b: Self) {}

    #[logic]
    #[open(self)]
    #[requires(self.valid())]
    #[ensures(
        (forall<b: Self> ! (b.incl(self) && b.idemp())) ||
        (exists<b: Self> b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b))
    )]
    fn maximal_idemp(self) {}
}
