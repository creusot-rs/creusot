use crate::{logic::ra::{update::Update, RA}, *};

/// The 'exclusive' Resource Algebra.
///
/// Combining those resource with [`RA::op`] **never** yields valid elements.
/// As such, only one version of this resource (when using
/// [`Resource`](crate::resource::Resource)) will be able to exists at a given moment.
pub struct Excl<T>(pub T);

impl<T> RA for Excl<T> {
    #[logic]
    #[open]
    fn op(self, _other: Self) -> Option<Self> {
        None
    }

    #[logic]
    #[open]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        None
    }

    #[logic]
    #[open]
    #[ensures(result == (self.op(self) == Some(self)))]
    fn idemp(self) -> bool {
        false
    }

    #[law]
    #[open(self)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[law]
    #[open(self)]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic]
    #[open(self)]
    #[ensures(match result {
        Some(b) => b.incl(self) && b.idemp() &&
           forall<c: Self> c.incl(self) && c.idemp() ==> c.incl(b),
        None => forall<b: Self> ! (b.incl(self) && b.idemp()),
    })]
    fn maximal_idemp(self) -> Option<Self> {
        None
    }
}

pub struct ExclUpdate<T>(pub Snapshot<T>);

impl<T> Update<Excl<T>> for ExclUpdate<T> {
    type Choice = ();

    #[logic]
    #[open]
    fn premise(self, _: Excl<T>) -> bool {
        true
    }

    #[logic]
    #[open]
    fn update(self, _: Excl<T>, _: ()) -> Excl<T> {
        Excl(*self.0)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: Excl<T>, frame: Excl<T>) {}
}
