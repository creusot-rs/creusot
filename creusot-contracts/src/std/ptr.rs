use crate::{
    ptr_own::{BlockOwn, RawPtr},
    *,
};
pub use ::std::ptr::*;

/// We conservatively model raw pointers as having an address *plus some hidden
/// metadata*.
///
/// This is to account for provenance
/// (<https://doc.rust-lang.org/std/ptr/index.html#using-strict-provenance>) and
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

    #[logic]
    #[ensures(result.addr_logic() == self.addr_logic())]
    fn raw(self) -> RawPtr<T>;
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

    #[logic]
    #[open]
    #[ensures(result.addr_logic() == self.addr_logic())]
    fn raw(self) -> RawPtr<T> {
        self
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

    #[trusted] // TODO cast *mut to *const
    #[logic]
    #[open]
    #[ensures(result.addr_logic() == self.addr_logic())]
    fn raw(self) -> RawPtr<T> {
        self as RawPtr<T>
    }
}

pub trait SizedPointerExt<T>: PointerExt<T> {
    /// Logic version of `add` for pointers.
    #[logic]
    #[ensures(self.addr_logic()@ + offset < usize::MAX@ ==> result.addr_logic()@ == self.addr_logic()@ + offset)]
    fn offset_logic(self, offset: Int) -> RawPtr<T>;

    /// Restriction of `add` that requires evidence that the addition is safe.
    /// We simply require a borrow of the `BlockOwn` token for the result pointer.
    /// In particular, this accounts for one-past-the-end pointers, which point to a zero-sized block.
    ///
    /// From https://doc.rust-lang.org/std/primitive.pointer.html#method.add:
    ///
    /// > If any of the following conditions are violated, the result is Undefined Behavior:
    /// > - The offset in bytes, `count * size_of::<T>()`, computed on mathematical
    /// >   integers (without “wrapping around”), must fit in an `isize`.
    /// > - If the computed offset is non-zero, then `self` must be derived from a
    /// >   pointer to some allocated object, and the entire memory range between
    /// >   `self` and the result must be in bounds of that allocated object.
    /// >   In particular, this range must not “wrap around” the edge of the address space.
    #[requires(own.ptr() == self.offset_logic(offset@))]
    #[ensures(own.ptr() == result.raw())]
    unsafe fn add_own(self, offset: usize, own: Ghost<&BlockOwn<T>>) -> Self;
}

impl<T> SizedPointerExt<T> for *const T {
    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(self.addr_logic()@ + offset < usize::MAX@ ==> result.addr_logic()@ == self.addr_logic()@ + offset)]
    fn offset_logic(self, offset: Int) -> RawPtr<T> {
        let _ = offset;
        dead
    }

    #[trusted]
    #[requires(own.ptr() == self.offset_logic(offset@))]
    #[ensures(own.ptr() == result.raw())]
    unsafe fn add_own(self, offset: usize, own: Ghost<&BlockOwn<T>>) -> Self {
        self.add(offset)
    }
}

impl<T> SizedPointerExt<T> for *mut T {
    #[trusted]
    #[logic]
    #[open(self)]
    #[ensures(self.addr_logic()@ + offset < usize::MAX@ ==> result.addr_logic()@ == self.addr_logic()@ + offset)]
    fn offset_logic(self, offset: Int) -> RawPtr<T> {
        let _ = offset;
        dead
    }

    #[trusted]
    #[requires(own.ptr() == self.offset_logic(offset@))]
    #[ensures(own.ptr() == result.raw())]
    unsafe fn add_own(self, offset: usize, own: Ghost<&BlockOwn<T>>) -> Self {
        self.add(offset)
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
}
