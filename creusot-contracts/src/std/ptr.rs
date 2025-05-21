use crate::{
    ptr_own::{PtrOwn, RawPtr},
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
    #[open(self)]
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
    #[open(self)]
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

pub trait SizedPointerExt<T> {
    /// Logic version of `add` for pointers.
    #[logic]
    fn offset_logic(self, offset: Int) -> RawPtr<T>;

    /// Restriction of `add` that requires evidence that the addition is safe.
    /// See contracts in implementations below.
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
    unsafe fn add_own(self, offset: usize, own_offset: Ghost<&PtrOwn<T>>) -> Self;
}

impl<T> SizedPointerExt<T> for *const T {
    #[trusted]
    #[logic]
    #[open(self)]
    fn offset_logic(self, offset: Int) -> RawPtr<T> {
        let _ = offset;
        dead
    }

    // TODO: The offset in bytes, `count * size_of::<T>()`, must fit in an `isize`.
    #[trusted]
    #[requires(self.offset_logic(offset@) == own_offset.ptr())]
    #[ensures(self.offset_logic(offset@) == result)]
    unsafe fn add_own(self, offset: usize, own_offset: Ghost<&PtrOwn<T>>) -> Self {
        self.add(offset)
    }
}

impl<T> SizedPointerExt<T> for *mut T {
    #[trusted]
    #[logic]
    #[open(self)]
    fn offset_logic(self, offset: Int) -> RawPtr<T> {
        let _ = offset;
        dead
    }

    // TODO: The offset in bytes, `count * size_of::<T>()`, must fit in an `isize`.
    #[trusted]
    #[requires(self.offset_logic(offset@) == own_offset.ptr())]
    // #[ensures(result as RawPtr<T> == self.offset_logic(offset))] // TODO: cast *mut to RawPtr ?
    unsafe fn add_own(self, offset: usize, own_offset: Ghost<&PtrOwn<T>>) -> Self {
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
