use creusot_std::{
    prelude::*,
    std::sync::view::{AcquireSyncView, ReleaseSyncView, SyncView},
};

use std::sync::atomic::{Ordering, fence};

#[ensures(*sync_view == result.view())]
#[trusted]
#[allow(unused_variables)]
pub fn fence_release(sync_view: Ghost<SyncView>) -> Ghost<ReleaseSyncView> {
    fence(Ordering::Release);
    Ghost::conjure()
}

#[ensures(acq_view.view() == *result)]
#[trusted]
#[allow(unused_variables)]
pub fn fence_acquire(acq_view: Ghost<AcquireSyncView>) -> Ghost<SyncView> {
    fence(Ordering::Acquire);
    Ghost::conjure()
}
