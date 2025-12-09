use crate::{
    logic::{Mapping, ops::IndexLogic},
    model::View,
    prelude::*,
};

#[logic(opaque)]
#[intrinsic("equal")]
pub fn equal<T: ?Sized>(_: T, _: T) -> bool {
    dead
}

#[logic(opaque)]
#[intrinsic("neq")]
pub fn neq<T: ?Sized>(_: T, _: T) -> bool {
    dead
}

#[logic(opaque)]
#[intrinsic("exists")]
pub fn exists<Tup: core::marker::Tuple, F: Fn<Tup, Output = bool>>(_: F) -> bool {
    dead
}

#[logic(opaque)]
#[intrinsic("forall")]
pub fn forall<Tup: core::marker::Tuple, F: Fn<Tup, Output = bool>>(_: F) -> bool {
    dead
}

#[logic(opaque)]
#[intrinsic("trigger")]
pub fn trigger<T, Trigger>(_: Trigger, _: T) -> T {
    dead
}

#[logic(opaque)]
#[intrinsic("implication")]
pub fn implication(_: bool, _: bool) -> bool {
    dead
}

#[cfg(feature = "std")]
#[logic(opaque)]
#[intrinsic("old")]
pub fn old<T: ?Sized>(_: T) -> &'static T {
    dead
}

#[cfg(feature = "std")]
#[logic(opaque)]
#[intrinsic("dead")]
#[allow(unconditional_recursion)]
pub fn dead<T: ?Sized>() -> &'static T {
    dead
}

#[logic(opaque)]
#[intrinsic("variant_check")]
pub fn variant_check<R: crate::logic::WellFounded>(_: R) -> R {
    dead
}

#[logic(opaque)]
#[intrinsic("closure_result")]
pub fn closure_result<R: ?Sized>(_: R, _: R) {}

#[check(ghost)]
#[trusted]
#[intrinsic("snapshot_from_fn")]
pub fn snapshot_from_fn<T: ?Sized, F: Fn() -> T>(_: F) -> Snapshot<T> {
    panic!()
}

#[logic(opaque)]
#[builtin("identity")]
pub fn mapping_from_fn<A: ?Sized, B, F: FnOnce(&A) -> B>(_: F) -> Mapping<A, B> {
    dead
}

#[logic(opaque)]
#[intrinsic("seq_literal")]
pub fn seq_literal<T>(_: &[T]) -> crate::logic::Seq<T> {
    dead
}

// The following three traits make it possible to leverage auto-deref for these operators
// without importing the traits in the context.

#[diagnostic::on_unimplemented(
    message = "the type `{Self}` cannot be indexed by `{I}` in logic",
    label = "`{Self}` cannot be indexed by `{I}` in logic"
)]
pub trait IndexLogicStub<I: ?Sized>: IndexLogic<I> {
    #[logic]
    #[intrinsic("index_logic_stub")]
    fn __creusot_index_logic_stub(self, idx: I) -> Self::Item;
}

#[diagnostic::do_not_recommend]
impl<I: ?Sized, T: ?Sized + IndexLogic<I>> IndexLogicStub<I> for T {
    #[logic(opaque)]
    fn __creusot_index_logic_stub(self, _idx: I) -> Self::Item {
        dead
    }
}

#[diagnostic::on_unimplemented(
    message = "Cannot take the view of `{Self}`",
    label = "no implementation for `{Self}@`"
)]
pub trait ViewStub: View {
    #[logic]
    #[intrinsic("view_stub")]
    fn __creusot_view_stub(self) -> Self::ViewTy;
}

#[diagnostic::do_not_recommend]
impl<T: ?Sized + View> ViewStub for T {
    #[logic(opaque)]
    fn __creusot_view_stub(self) -> Self::ViewTy {
        dead
    }
}
