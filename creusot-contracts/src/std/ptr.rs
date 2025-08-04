use crate::*;
pub use ::std::ptr::*;

/// We conservatively model raw pointers as having an address *plus some hidden
/// metadata*.
///
/// This is to account for provenance
/// (<https://doc.rust-lang.org/std/ptr/index.html#[check(ghost)]sing-strict-provenance>) and
/// wide pointers. See e.g.
/// <https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null>: "unsized
/// types have many possible null pointers, as only the raw data pointer is
/// considered, not their length, vtable, etc. Therefore, two pointers that are
/// null may still not compare equal to each other."
#[allow(dead_code)]
pub struct PtrDeepModel {
    pub addr: usize,
    runtime_metadata: usize,
}

impl<T: ?Sized> DeepModel for *mut T {
    type DeepModelTy = PtrDeepModel;
    #[logic]
    #[trusted]
    #[ensures(result.addr == self.addr_logic())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { dead }
    }
}

impl<T: ?Sized> DeepModel for *const T {
    type DeepModelTy = PtrDeepModel;
    #[logic]
    #[trusted]
    #[ensures(result.addr == self.addr_logic())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { dead }
    }
}

pub trait PointerExt<T: ?Sized>: Sized {
    /// _logical_ address of the pointer
    #[logic]
    fn addr_logic(self) -> usize;

    #[logic]
    #[ensures(result == (self.addr_logic() == 0usize))]
    fn is_null_logic(self) -> bool;
}

impl<T: ?Sized> PointerExt<T> for *const T {
    #[trusted]
    #[logic]
    fn addr_logic(self) -> usize {
        dead
    }

    #[logic]
    #[open]
    #[ensures(result == (self.addr_logic() == 0usize))]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0usize
    }
}

impl<T: ?Sized> PointerExt<T> for *mut T {
    #[trusted]
    #[logic]
    fn addr_logic(self) -> usize {
        dead
    }

    #[logic]
    #[open]
    #[ensures(result == (self.addr_logic() == 0usize))]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0usize
    }
}

extern_spec! {
    impl<T> *const T {
        #[ensures(result == self.addr_logic())]
        fn addr(self) -> usize;

        #[ensures(result == self.is_null_logic())]
        fn is_null(self) -> bool;
    }

    impl<T> *mut T {
        #[ensures(result == self.addr_logic())]
        fn addr(self) -> usize;

        #[ensures(result == self.is_null_logic())]
        fn is_null(self) -> bool;
    }

    mod std {
        mod ptr {
            #[ensures(result.is_null_logic())]
            fn null<T>() -> *const T
            where
                T: std::ptr::Thin + ?Sized;

            #[ensures(result.is_null_logic())]
            fn null_mut<T>() -> *mut T
            where
                T: std::ptr::Thin + ?Sized;

            #[ensures(result == (p.addr_logic() == q.addr_logic()))]
            fn addr_eq<T, U>(p: *const T, q: *const U) -> bool
            where
                T: ?Sized, U: ?Sized;
        }
    }

    impl<T> Clone for *mut T {
        #[ensures(result == *self)]
        fn clone(&self) -> *mut T {
            *self
        }
    }

    impl<T> Clone for *const T {
        #[ensures(result == *self)]
        fn clone(&self) -> *const T {
            *self
        }
    }
}
