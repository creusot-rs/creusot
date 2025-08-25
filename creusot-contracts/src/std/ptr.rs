use crate::{
    ghost::PtrOwn,
    *,
};
#[cfg(creusot)]
use crate::std::mem::size_of_logic;
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
    pub addr: Int,
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
    fn addr_logic(self) -> Int;

    /// `true` if the pointer is null.
    #[logic]
    #[ensures(result == (self.addr_logic() == 0))]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0
    }
}

impl<T: ?Sized> PointerExt<T> for *const T {
    #[trusted]
    #[logic]
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

pub trait SizedPointerExt<T>: PointerExt<T> {
    #[logic]
    #[ensures(result.addr_logic() == self.addr_logic() + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> *const T;

    #[law]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int);
}

impl<T> SizedPointerExt<T> for *const T {
    #[trusted]
    #[logic]
    #[ensures(result.addr_logic() == self.addr_logic() + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> *const T {
        dead
    }

    #[trusted]
    #[law]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int) {}
}

pub trait SlicePointerExt<T>: PointerExt<[T]> {
    #[logic]
    fn as_ptr_logic(self) -> *const T;

    #[logic]
    fn len_logic(self) -> Int;

    #[law]
    #[ensures(self.as_ptr_logic() == other.as_ptr_logic() && self.len_logic() == other.len_logic() ==> self == other)]
    fn slice_ptr_ext(self, other: Self);
}

impl<T> SlicePointerExt<T> for *const [T] {
    #[trusted]
    #[logic]
    fn as_ptr_logic(self) -> *const T {
        dead
    }

    #[trusted]
    #[logic]
    fn len_logic(self) -> Int {
        dead
    }

    #[trusted]
    #[law]
    #[ensures(self.as_ptr_logic() == other.as_ptr_logic() && self.len_logic() == other.len_logic() ==> self == other)]
    fn slice_ptr_ext(self, other: Self) {}
}

pub trait PtrAddExt<T>: PointerExt<T> {
    /// Restriction of `add` that requires evidence that the addition is safe.
    /// We simply require a borrow of the `PtrOwn<[T]>` token for the result pointer.
    /// In particular, this accounts for one-past-the-end pointers, which point to a zero-sized slice.
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
    ///
    ///
    #[requires(false)]
    unsafe fn add_own(self, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> Self;
}

impl<T> PtrAddExt<T> for *const T {
    #[trusted]
    #[requires(own.ptr().as_ptr_logic() == self.offset_logic(offset@))]
    #[ensures(own.ptr().as_ptr_logic() == result)]
    unsafe fn add_own(self, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> Self {
        self.add(offset)
    }
}

impl<T> PtrAddExt<T> for *mut T {
    #[trusted]
    #[requires(own.ptr().as_ptr_logic() == (self as *const T).offset_logic(offset@))]
    #[ensures(own.ptr().as_ptr_logic() == result as *const T)]
    unsafe fn add_own(self, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> Self {
        self.add(offset)
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

    impl<T> *const [T] {
        #[ensures(result@ == self.len_logic())]
        fn len(self) -> usize;
    }

    impl<T> *mut [T] {
        #[ensures(result@ == self.len_logic())]
        fn len(self) -> usize;
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

            #[ensures(result.as_ptr_logic() == data && result.len_logic() == len@)]
            fn slice_from_raw_parts<T>(data: *const T, len: usize) -> *const [T];

            #[ensures((result as *const [T]).as_ptr_logic() == data as *const T && (result as *const [T]).len_logic() == len@)]
            fn slice_from_raw_parts_mut<T>(data: *mut T, len: usize) -> *mut [T];
        }
    }

    impl<T> Clone for *mut T {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> *mut T {
            *self
        }
    }

    impl<T> Clone for *const T {
        #[check(ghost)]
        #[ensures(result == *self)]
        fn clone(&self) -> *const T {
            *self
        }
    }
}
