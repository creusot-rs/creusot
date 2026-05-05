use crate::prelude::*;
use core::{marker::PhantomData, panic};

#[cfg(creusot)]
use core::cmp::Ordering;

#[cfg(creusot)]
use crate::ghost::Objective;

pub type Timestamp = Int;

pub trait HasTimestamp {
    #[logic]
    fn get_timestamp(self, view: SyncView) -> Timestamp;

    #[logic(law)]
    #[requires(x <= y)]
    #[ensures(self.get_timestamp(x) <= self.get_timestamp(y))]
    fn get_timestamp_monotonic(self, x: SyncView, y: SyncView);
}

/// A witness to the _current view_, containing all the events observed by this thread.
///
/// In Cosmo, [`SyncView`] corresponds to the notation `↑V`
/// In Relaxed RustBelt, [`SyncView`] corresponds to the notation `V.cur`
#[opaque]
#[derive(Copy)]
pub struct SyncView(());

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

    #[check(ghost)]
    #[trusted]
    #[requires(*to <= *self)]
    #[ensures(^self == *to)]
    #[allow(unused_variables)]
    pub fn weaken(&mut self, to: Snapshot<SyncView>) {
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

/// A witness to the _release view_, containing all the events observed by this thread at its last release fence.
///
/// In Relaxed RustBelt, [`SyncView`] corresponds to the notation `V.rel`
#[opaque]
#[derive(Copy)]
pub struct ReleaseSyncView(());

impl Clone for ReleaseSyncView {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl ReleaseSyncView {
    #[check(ghost)]
    #[trusted]
    pub fn new() -> Ghost<Self> {
        panic!("Should not be called outside ghost code")
    }

    #[check(ghost)]
    #[trusted]
    #[requires(*to <= (*self)@)]
    #[ensures((^self)@ == *to)]
    #[allow(unused_variables)]
    pub fn weaken(&mut self, to: Snapshot<SyncView>) {
        panic!("Should not be called outside ghost code")
    }
}

impl View for ReleaseSyncView {
    type ViewTy = SyncView;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

/// A witness to the _acquire view_, containing all the events that will be observed by this thread at its next acquire fence.
///
/// In Relaxed RustBelt, [`SyncView`] corresponds to the notation `V.acq`
#[opaque]
#[derive(Copy)]
pub struct AcquireSyncView(());

impl Clone for AcquireSyncView {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl AcquireSyncView {
    #[check(ghost)]
    #[trusted]
    pub fn new() -> Ghost<Self> {
        panic!("Should not be called outside ghost code")
    }

    #[check(ghost)]
    #[trusted]
    #[requires(*to <= (*self)@)]
    #[ensures((^self)@ == *to)]
    #[allow(unused_variables)]
    pub fn weaken(&mut self, to: Snapshot<SyncView>) {
        panic!("Should not be called outside ghost code")
    }
}

impl View for AcquireSyncView {
    type ViewTy = SyncView;

    #[logic(opaque)]
    fn view(self) -> Self::ViewTy {
        dead
    }
}

/// Resources that are held in view V.
///
/// In Cosmo, [`AtView`] corresponds to the notation `T@V`
/// In Relaxed RustBelt, [`AtView`] corresponds to the notation `@V T`
pub struct AtView<T>(PhantomData<T>);

#[cfg(creusot)]
#[trusted]
impl<T> Objective for AtView<T> {}

impl<T> AtView<T> {
    #[logic(opaque)]
    pub fn view(&self) -> SyncView {
        dead
    }

    #[logic(opaque)]
    pub fn val(&self) -> T {
        dead
    }

    #[check(ghost)]
    #[trusted]
    #[ensures(result.0 == result.1.view() && result.1.val() == *val)]
    #[allow(unused_variables)]
    pub fn new(val: Ghost<T>) -> Ghost<(SyncView, Self)> {
        Ghost::conjure()
    }

    #[check(ghost)]
    #[trusted]
    #[requires(self.view() <= sync_view)]
    #[ensures(result == self.val())]
    #[allow(unused_variables)]
    pub fn sync(self, sync_view: SyncView) -> T {
        panic!("Should not be called outside ghost code")
    }

    #[check(ghost)]
    #[trusted]
    #[requires(self.view() <= *to)]
    #[ensures((^self).view() == *to)]
    #[ensures((*self).val() == (^self).val())]
    #[allow(unused_variables)]
    pub fn weaken(&mut self, to: Snapshot<SyncView>) {
        panic!("Should not be called outside ghost code")
    }
}
