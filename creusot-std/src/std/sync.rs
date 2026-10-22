pub mod atomic;
#[cfg(feature = "sc-drf")]
pub mod atomic_sc;
pub mod committer;
pub mod view;

#[cfg(feature = "nightly")]
use crate::prelude::*;

#[cfg(feature = "std")]
mod arc;
#[cfg(feature = "std")]
pub use arc::*;

#[cfg(feature = "nightly")]
pub trait SyncViewExt<T: ?Sized> {
    unsafe fn borrow_mut<'a>(&'a self) -> &'a mut T;
}

#[cfg(feature = "nightly")]
impl<T: ?Sized> SyncViewExt<T> for core::cell::SyncUnsafeCell<T> {
    #[trusted]
    unsafe fn borrow_mut<'a>(&'a self) -> &'a mut T {
        unsafe { &mut *self.get() }
    }
}
