use super::PointerExt;
use crate::prelude::*;
use core::ptr::NonNull;

impl<T: ?Sized> View for NonNull<T> {
    type ViewTy = *mut T;
    #[logic(opaque)]
    fn view(self) -> *mut T {
        dead
    }
}

/// Additional lemmas for [`NonNull`].
pub trait NonNullExt {
    #[logic]
    fn view_inj(n1: Self, n2: Self);
}

impl<T: ?Sized> NonNullExt for NonNull<T> {
    /// Asserts that the `NonNull` is only defined by the contained pointer.
    #[logic]
    #[trusted]
    #[ensures(n1@ == n2@ ==> n1 == n2)]
    fn view_inj(n1: Self, n2: Self) {}
}

impl<T: ?Sized> DeepModel for NonNull<T> {
    type DeepModelTy = <*mut T as DeepModel>::DeepModelTy;
    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self.view().deep_model()
    }
}

impl<T: ?Sized> PointerExt<T> for NonNull<T> {
    #[logic(open, inline)]
    fn addr_logic(self) -> usize {
        self.view().addr_logic()
    }

    #[logic(open, inline)]
    fn is_aligned_logic(self) -> bool {
        self.view().is_aligned_logic()
    }
}

impl<T: ?Sized> Invariant for NonNull<T> {
    #[logic(open)]
    fn invariant(self) -> bool {
        !self.is_null_logic()
    }
}

extern_spec! {
    impl<T> NonNull<T> {
        #[ensures(result.is_aligned_logic())]
        const fn dangling() -> NonNull<T>;
    }

    impl<T> NonNull<T>
        where T: ?Sized
    {
        #[requires(!ptr.is_null_logic())]
        #[ensures(result@ == ptr)]
        const unsafe fn new_unchecked(ptr: *mut T) -> NonNull<T>;

        #[ensures(match result {
            None => ptr.is_null_logic(),
            Some(res) => res@ == ptr,
        })]
        const fn new(ptr: *mut T) -> Option<NonNull<T>>;

        #[ensures(result.is_aligned_logic())]
        const fn from_ref(r: &T) -> NonNull<T>;

        #[ensures(result.is_aligned_logic())]
        const fn from_mut(r: &mut T) -> NonNull<T>;

        #[ensures(result == self@)]
        const fn as_ptr(self) -> *mut T;

        #[ensures(result@ == self@ as *mut U)]
        const fn cast<U>(self) -> NonNull<U>;
    }

    impl<T> Clone for NonNull<T>
        where T: ?Sized
    {
        #[ensures(result == *self)]
        fn clone(&self) -> Self {
            *self
        }
    }
}
