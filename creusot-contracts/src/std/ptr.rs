use crate::*;
pub use ::std::ptr::*;

/// We conservatively model raw pointers as having an address *plus some hidden
/// metadata*.
///
/// This is to account for provenance
/// (https://doc.rust-lang.org/std/ptr/index.html#using-strict-provenance) and
/// wide pointers. See e.g.
/// https://doc.rust-lang.org/std/primitive.pointer.html#method.is_null: "unsized
/// types have many possible null pointers, as only the raw data pointer is
/// considered, not their length, vtable, etc. Therefore, two pointers that are
/// null may still not compare equal to each other."

#[allow(dead_code)]
pub struct PtrDeepModel {
    pub addr: Int,
    runtime_metadata: usize,
}

impl<T: ?Sized> DeepModel for *mut T {
    type DeepModelTy = PtrDeepModel;
    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result.addr == self.addr_logic())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { dead }
    }
}

impl<T: ?Sized> DeepModel for *const T {
    type DeepModelTy = PtrDeepModel;
    #[logic]
    #[trusted]
    #[open(self)]
    #[ensures(result.addr == self.addr_logic())]
    fn deep_model(self) -> Self::DeepModelTy {
        pearlite! { dead }
    }
}

impl<T: ?Sized> View for *mut T {
    type ViewTy = Int;
    #[logic]
    #[open]
    fn view(self) -> Int {
        self.addr_logic()
    }
}

impl<T: ?Sized> View for *const T {
    type ViewTy = Int;
    #[logic]
    #[open]
    fn view(self) -> Int {
        self.addr_logic()
    }
}

pub trait PointerExt<T: ?Sized>: Sized {
    #[logic]
    fn addr_logic(self) -> Int;

    #[logic]
    #[ensures(result == (self.addr_logic() == 0))]
    fn is_null_logic(self) -> bool;
}

impl<T: ?Sized> PointerExt<T> for *const T {
    #[trusted]
    #[logic]
    #[open(self)]
    fn addr_logic(self) -> Int {
        dead
    }

    #[logic]
    #[open]
    #[ensures(result == (self.addr_logic() == 0))]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0
    }
}

impl<T: ?Sized> PointerExt<T> for *mut T {
    #[trusted]
    #[logic]
    #[open(self)]
    fn addr_logic(self) -> Int {
        dead
    }

    #[logic]
    #[open]
    #[ensures(result == (self.addr_logic() == 0))]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0
    }
}

extern_spec! {
    impl<T> *const T {
        #[ensures(result@ == self.addr_logic())]
        fn addr(self) -> usize;

        #[ensures(result == self.is_null_logic())]
        fn is_null(self) -> bool;
    }

    impl<T> *mut T {
        #[ensures(result@ == self.addr_logic())]
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
}
