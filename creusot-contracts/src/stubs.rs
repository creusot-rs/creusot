use crate::*;

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
pub fn exists<Tup: std::marker::Tuple, F: Fn<Tup, Output = bool>>(_: F) -> bool {
    dead
}

#[logic(opaque)]
#[intrinsic("forall")]
pub fn forall<Tup: std::marker::Tuple, F: Fn<Tup, Output = bool>>(_: F) -> bool {
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

#[logic(opaque)]
#[intrinsic("old")]
pub fn old<T: ?Sized>(_: T) -> Box<T> {
    dead
}

#[logic(opaque)]
#[intrinsic("dead")]
#[allow(unconditional_recursion)]
pub fn dead<T: ?Sized>() -> Box<T> {
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
pub fn snapshot_from_fn<T: ?Sized, F: Fn() -> crate::Snapshot<T>>(_: F) -> crate::Snapshot<T> {
    panic!()
}

#[logic(opaque)]
#[builtin("identity")]
pub fn mapping_from_fn<A: ?Sized, B, F: FnOnce(&A) -> B>(_: F) -> crate::logic::Mapping<A, B> {
    dead
}

#[logic(opaque)]
#[intrinsic("seq_literal")]
pub fn seq_literal<T>(_: &[T]) -> crate::logic::Seq<T> {
    dead
}
