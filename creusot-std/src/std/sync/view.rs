use crate::{ghost::NotObjective, prelude::*};
use core::{marker::PhantomData, panic};

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
pub struct SyncView(NotObjective);

impl Clone for SyncView {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl SyncView {
    #[check(ghost)]
    #[trusted]
    pub const fn new() -> Ghost<Self> {
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

    #[logic(opaque)]
    #[ensures(self >= result)]
    #[ensures(other >= result)]
    #[ensures(forall<r> self >= r ==> other >= r ==> result >= r)]
    #[trusted]
    pub fn meet(self, other: Self) -> Self {
        dead
    }
}

impl PartialOrdLogic for SyncView {
    #[logic(opaque)]
    fn lt_log(self, _: Self) -> bool {
        dead
    }

    #[logic(law)]
    #[ensures(!(self < self))]
    #[trusted]
    fn irreflexive(self) {}

    #[logic(law)]
    #[requires(x < y)]
    #[requires(y < z)]
    #[ensures(x < z)]
    #[trusted]
    fn transitive(x: Self, y: Self, z: Self) {}

    #[logic(law)]
    #[ensures((self <= other) == (self < other || self == other))]
    fn le_lt_log(self, other: Self) {}
}

/// A witness to the _release view_, containing all the events observed by this thread at its last release fence.
///
/// In Relaxed RustBelt, [`SyncView`] corresponds to the notation `V.rel`
#[opaque]
#[derive(Copy)]
#[allow(dead_code)]
pub struct ReleaseSyncView(*mut ()); // Neither Sync nor Send

impl Clone for ReleaseSyncView {
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl From<ReleaseSyncView> for SyncView {
    #[check(ghost)]
    #[ensures(result == value@)]
    #[trusted]
    #[allow(unused_variables)]
    fn from(value: ReleaseSyncView) -> Self {
        panic!("Should not be called outside ghost code")
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
#[allow(dead_code)]
pub struct AcquireSyncView(*mut ()); // Neither Sync nor Send

impl Clone for AcquireSyncView {
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        *self
    }
}

impl From<SyncView> for AcquireSyncView {
    #[check(ghost)]
    #[ensures(result@ == value)]
    #[trusted]
    #[allow(unused_variables)]
    fn from(value: SyncView) -> Self {
        panic!("Should not be called outside ghost code")
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
