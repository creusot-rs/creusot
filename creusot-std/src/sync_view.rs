use crate::prelude::*;
use core::marker::PhantomData;

#[cfg(creusot)]
use core::cmp::Ordering;

/// An assertion whose meaning is independent of this thread's view.
///
/// Since `Objective` refers to ghost objects whose memory is objective, Rust's
/// `Unique<T>` (and therefore `Box<T>`, `Vec<T>`, ...) are therefore objective.
#[cfg(creusot)]
#[trusted]
pub auto trait Objective {}

/// A guard for potentially subjective types
///
/// Some types, such as `Perm`, could hold a permission to access a value that
/// depends on the view.
///
/// This negative implementation primarily targets `Perm<PermCell<T>>` and
/// `Perm<*const T>`.
pub(crate) struct NotObjective {}

#[cfg(creusot)]
#[trusted]
impl !Objective for NotObjective {}

pub type Timestamp = Int;

pub trait HasTimestamp {
    #[logic]
    fn get_timestamp(self, view: SyncView) -> Timestamp;

    #[logic(law)]
    #[requires(x.le_log(y))]
    #[ensures(self.get_timestamp(x).le_log(self.get_timestamp(y)))]
    fn get_timestamp_monotonic(self, x: SyncView, y: SyncView);
}

/// ↑V
// TODO: [VL] Send issue opaque + Clone
#[opaque]
#[derive(Copy)]
pub struct SyncView;

impl Clone for SyncView {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl SyncView {
    #[check(ghost)]
    #[trusted]
    pub fn new() -> Ghost<Self> {
        panic!("Should not be called outside ghost code")
    }
}

impl OrdLogic for SyncView {
    #[logic(opaque)]
    fn cmp_log(self, _: Self) -> Ordering {
        dead
    }

    #[logic(law)]
    #[ensures(x.le_log(y) == (x.cmp_log(y) != Ordering::Greater))]
    #[trusted]
    fn cmp_le_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.lt_log(y) == (x.cmp_log(y) == Ordering::Less))]
    #[trusted]
    fn cmp_lt_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.ge_log(y) == (x.cmp_log(y) != Ordering::Less))]
    #[trusted]
    fn cmp_ge_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.gt_log(y) == (x.cmp_log(y) == Ordering::Greater))]
    #[trusted]
    fn cmp_gt_log(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures(x.cmp_log(x) == Ordering::Equal)]
    #[trusted]
    fn refl(x: Self) {}

    #[logic(law)]
    #[requires(x.cmp_log(y) == o)]
    #[requires(y.cmp_log(z) == o)]
    #[ensures(x.cmp_log(z) == o)]
    #[trusted]
    fn trans(x: Self, y: Self, z: Self, o: Ordering) {}

    #[logic(law)]
    #[requires(x.cmp_log(y) == Ordering::Less)]
    #[ensures(y.cmp_log(x) == Ordering::Greater)]
    #[trusted]
    fn antisym1(x: Self, y: Self) {}

    #[logic(law)]
    #[requires(x.cmp_log(y) == Ordering::Greater)]
    #[ensures(y.cmp_log(x) == Ordering::Less)]
    #[trusted]
    fn antisym2(x: Self, y: Self) {}

    #[logic(law)]
    #[ensures((x == y) == (x.cmp_log(y) == Ordering::Equal))]
    #[trusted]
    fn eq_cmp(x: Self, y: Self) {}
}

/// P@V
pub struct AtView<T>(PhantomData<T>);

#[cfg(creusot)]
#[trusted]
impl<T> Objective for AtView<T> {}

impl<T> AtView<T> {
    #[logic(opaque)]
    pub fn view_logic(&self) -> SyncView {
        dead
    }

    #[logic(opaque)]
    pub fn value(&self) -> T {
        dead
    }

    #[check(ghost)]
    #[trusted]
    #[ensures(result.0 == result.1.view_logic() && result.1.value() == *val)]
    #[allow(unused_variables)]
    pub fn new(val: Ghost<T>) -> Ghost<(SyncView, Self)> {
        Ghost::conjure()
    }

    #[check(ghost)]
    #[trusted]
    #[requires(self.view_logic().le_log(v))]
    #[ensures(result == self.value())]
    #[allow(unused_variables)]
    pub fn into_inner(self, v: SyncView) -> T {
        panic!("Should not be called outside ghost code")
    }

    #[check(ghost)]
    #[trusted]
    #[ensures(result == self.view_logic())]
    pub fn view(&self) -> SyncView {
        panic!("Should not be called outside ghost code")
    }
}
