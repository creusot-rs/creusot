use creusot_std::{
    prelude::*,
    sync_view::{AcquireSyncView, ReleaseSyncView, SyncView},
};

#[ensures(*sync_view <= result.view())]
#[trusted]
#[allow(unused_variables)]
pub fn fence_release(sync_view: Ghost<SyncView>) -> Ghost<ReleaseSyncView> {
    ::std::sync::atomic::fence(::std::sync::atomic::Ordering::Release);
    Ghost::conjure()
}

#[ensures(acq_view.view() <= *result)]
#[trusted]
#[allow(unused_variables)]
pub fn fence_acquire(acq_view: Ghost<AcquireSyncView>) -> Ghost<SyncView> {
    ::std::sync::atomic::fence(::std::sync::atomic::Ordering::Acquire);
    Ghost::conjure()
}
