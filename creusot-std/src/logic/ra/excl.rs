use crate::{
    logic::ra::{RA, update::Update},
    prelude::*,
};

/// The 'exclusive' Resource Algebra.
///
/// Combining those resource with [`RA::op`] **never** yields valid elements.
/// As such, only one version of this resource (when using
/// [`Resource`][crate::ghost::resource::Resource]) will be able to exist at a given moment.
pub struct Excl<T>(pub T);

impl<T> RA for Excl<T> {
    #[logic(open)]
    fn op(self, _other: Self) -> Option<Self> {
        None
    }

    #[logic(open)]
    #[ensures(match result {
        Some(c) => factor.op(c) == Some(self),
        None => forall<c: Self> factor.op(c) != Some(self),
    })]
    fn factor(self, factor: Self) -> Option<Self> {
        None
    }

    #[logic(law)]
    #[ensures(a.op(b) == b.op(a))]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[ensures(a.op(b).and_then_logic(|ab: Self| ab.op(c)) == b.op(c).and_then_logic(|bc| a.op(bc)))]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        None
    }

    #[logic]
    #[requires(self.core() != None)]
    #[ensures({
        let c = self.core().unwrap_logic();
        c.op(c) == Some(c)
    })]
    #[ensures(self.core().unwrap_logic().op(self) == Some(self))]
    fn core_idemp(self) {}

    #[logic]
    #[requires(i.op(i) == Some(i))]
    #[requires(i.op(self) == Some(self))]
    #[ensures(match self.core() {
        Some(c) => i.incl(c),
        None => false,
    })]
    fn core_is_maximal_idemp(self, i: Self) {}
}

/// Apply an [update](Update) to the content of an [exclusive](Excl) resource.
///
/// This changes the content of the resource. Because it is exclusive, no
/// premise is needed.
///
/// # Example
///
/// ```
/// use creusot_std::{prelude::*, logic::ra::excl::{Excl, ExclUpdate}, ghost::resource::Resource};
/// let mut res = Resource::alloc(snapshot!(Excl(1)));
/// ghost! { res.update(ExclUpdate(snapshot!(2))) };
/// proof_assert!(res@ == Excl(2));
/// ```
pub struct ExclUpdate<T>(pub Snapshot<T>);

impl<T> Update<Excl<T>> for ExclUpdate<T> {
    type Choice = ();

    #[logic(open, inline)]
    fn premise(self, _: Excl<T>) -> bool {
        true
    }

    #[logic(open, inline)]
    #[requires(self.premise(from))]
    fn update(self, from: Excl<T>, _: ()) -> Excl<T> {
        Excl(*self.0)
    }

    #[logic]
    #[requires(self.premise(from))]
    #[requires(from.op(frame) != None)]
    #[ensures(self.update(from, result).op(frame) != None)]
    fn frame_preserving(self, from: Excl<T>, frame: Excl<T>) {}
}
