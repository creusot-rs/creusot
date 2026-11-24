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
    #[allow(unused_variables)]
    fn incl(self, other: Self) -> bool {
        false
    }

    #[logic(law)]
    #[allow(unused_variables)]
    fn commutative(a: Self, b: Self) {}

    #[logic]
    #[allow(unused_variables)]
    fn associative(a: Self, b: Self, c: Self) {}

    #[logic(open)]
    fn core(self) -> Option<Self> {
        None
    }

    #[logic]
    fn core_idemp(self) {}

    #[logic]
    #[allow(unused_variables)]
    fn core_is_maximal_idemp(self, i: Self) {}

    #[logic(open)]
    fn cancelable(self) -> bool {
        true
    }
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
