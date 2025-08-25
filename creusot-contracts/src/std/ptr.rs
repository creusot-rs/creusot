#[cfg(creusot)]
use crate::std::mem::{align_of_logic, size_of_logic};
use crate::{ghost::PtrOwn, *};
pub use ::std::ptr::*;

/// Metadata of a pointer in logic.
///
/// [`std::ptr::metadata`] in logic.
#[logic(opaque)]
pub fn metadata_logic<T: ?Sized>(_: *const T) -> <T as Pointee>::Metadata {
    dead
}

/// Check that a value is compatible with some metadata.
///
/// If the value is a slice, this predicate asserts that the metadata equals the length of the slice,
/// and that the total size of the slice is no more than `isize::MAX`. This latter property is assumed
/// by pointer primitives such as [`slice::from_raw_parts`][from_raw_parts].
///
/// - For `T = [U]`, specializes to [`metadata_matches_slice`].
/// - For `T = str`, specializes to [`metadata_matches_str`].
/// - For `T: Sized`, specializes to `true`.
///
/// Why did we not make this a function `fn metadata_of(value: T) -> <T as Pointee>::Metadata`?
/// Because this way is shorter: this corresponds to a single predicate in Why3 per type `T`.
/// Defining a logic function that returns `usize` for slices is not so
/// straightforward because almost every number wants to be `Int`.
/// We would need to generate one abstract Why3 function `metadata_of : T -> Metadata`
/// and an axiom `view_usize (metadata_of value) = len (Slice.view value)`,
/// so two Why3 declarations instead of one.
///
/// [from_raw_parts]: https://doc.rust-lang.org/core/slice/fn.from_raw_parts.html
#[logic(open)]
#[intrinsic("metadata_matches")]
pub fn metadata_matches<T: ?Sized>(_value: T, _metadata: <T as Pointee>::Metadata) -> bool {
    dead
}

/// Definition of [`metadata_matches`] for slices.
#[logic(open)]
#[intrinsic("metadata_matches_slice")]
pub fn metadata_matches_slice<T>(value: [T], len: usize) -> bool {
    pearlite! { value@.len() == len@ && len@ * size_of_logic::<T>() <= isize::MAX@ }
}

/// Definition of [`metadata_matches`] for string slices.
#[logic(open)]
#[intrinsic("metadata_matches_str")]
pub fn metadata_matches_str(value: str, len: usize) -> bool {
    pearlite! { value@.to_bytes().len() == len@ && len@ <= isize::MAX@ }
}

/// Whether a pointer is aligned.
///
/// This is a logic version of [`<*const T>::is_aligned`][is_aligned],
/// but extended with an additional rule for `[U]`. We make use of this property
/// in [`ghost::PtrOwn`] to define a more precise invariant for slice pointers.
///
/// - For `T: Sized`, specializes to [`is_aligned_logic_sized`].
/// - For `T = [U]`, specializes to [`is_aligned_logic_slice`].
/// - For `T = str`, specializes to `true`.
///
/// [is_aligned]: https://doc.rust-lang.org/std/primitive.pointer.html#method.is_aligned
#[allow(unused_variables)]
#[logic(open)]
#[intrinsic("is_aligned_logic")]
pub fn is_aligned_logic<T: ?Sized>(ptr: *const T) -> bool {
    dead
}

/// Definition of [`is_aligned_logic`] for `T: Sized`.
#[logic(open)]
#[intrinsic("is_aligned_logic_sized")]
pub fn is_aligned_logic_sized<T>(ptr: *const T) -> bool {
    ptr.is_aligned_to_logic(align_of_logic::<T>())
}

/// Definition of [`is_aligned_logic`] for `[T]`.
#[logic(open)]
#[intrinsic("is_aligned_logic_slice")]
pub fn is_aligned_logic_slice<T>(ptr: *const [T]) -> bool {
    ptr.is_aligned_to_logic(align_of_logic::<T>())
}

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
    #[trusted]
    #[logic(opaque)]
    #[ensures(result.addr == self.addr_logic())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

impl<T: ?Sized> DeepModel for *const T {
    type DeepModelTy = PtrDeepModel;
    #[trusted]
    #[logic(opaque)]
    #[ensures(result.addr == self.addr_logic())]
    fn deep_model(self) -> Self::DeepModelTy {
        dead
    }
}

pub trait PointerExt<T: ?Sized>: Sized {
    /// _logical_ address of the pointer
    #[logic]
    fn addr_logic(self) -> usize;

    /// `true` if the pointer is null.
    #[logic(open, sealed)]
    fn is_null_logic(self) -> bool {
        self.addr_logic() == 0usize
    }

    /// Logic counterpart to [`<*const T>::is_aligned_to`][is_aligned_to]
    ///
    /// [is_aligned_to]: https://doc.rust-lang.org/std/primitive.pointer.html#method.is_aligned_to
    #[logic(open, sealed)]
    fn is_aligned_to_logic(self, align: usize) -> bool {
        pearlite! { self.addr_logic() & (align - 1usize) == 0usize }
    }

    /// Logic counterpart to [`<*const T>::is_aligned`][is_aligned]
    ///
    /// This is defined as [`is_aligned_logic`] (plus a noop coercion for `*mut T`).
    ///
    /// [is_aligned]: https://doc.rust-lang.org/std/primitive.pointer.html#method.is_aligned
    #[logic]
    fn is_aligned_logic(self) -> bool;
}

impl<T: ?Sized> PointerExt<T> for *const T {
    #[logic]
    #[cfg_attr(target_pointer_width = "16", builtin("creusot.prelude.Ptr$BW$.addr_logic_u16"))]
    #[cfg_attr(target_pointer_width = "32", builtin("creusot.prelude.Ptr$BW$.addr_logic_u32"))]
    #[cfg_attr(target_pointer_width = "64", builtin("creusot.prelude.Ptr$BW$.addr_logic_u64"))]
    fn addr_logic(self) -> usize {
        dead
    }

    #[logic(open, inline)]
    fn is_aligned_logic(self) -> bool {
        is_aligned_logic(self)
    }
}

impl<T: ?Sized> PointerExt<T> for *mut T {
    #[logic]
    #[cfg_attr(target_pointer_width = "16", builtin("creusot.prelude.Ptr$BW$.addr_logic_u16"))]
    #[cfg_attr(target_pointer_width = "32", builtin("creusot.prelude.Ptr$BW$.addr_logic_u32"))]
    #[cfg_attr(target_pointer_width = "64", builtin("creusot.prelude.Ptr$BW$.addr_logic_u64"))]
    fn addr_logic(self) -> usize {
        dead
    }

    #[logic(open, inline)]
    fn is_aligned_logic(self) -> bool {
        is_aligned_logic(self)
    }
}

pub trait SizedPointerExt<T>: PointerExt<T> {
    #[logic]
    #[ensures(self.addr_logic()@ + offset * size_of_logic::<T>() < usize::MAX@ ==> result.addr_logic()@ == self.addr_logic()@ + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> *const T;

    #[logic(law)]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int);
}

impl<T> SizedPointerExt<T> for *const T {
    #[trusted]
    #[logic(opaque)]
    #[ensures(self.addr_logic()@ + offset * size_of_logic::<T>() < usize::MAX@ ==> result.addr_logic()@ == self.addr_logic()@ + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> *const T {
        dead
    }

    #[trusted]
    #[logic(law)]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int) {}
}

/// Extension methods for `*const [T]`
pub trait SlicePointerExt<T>: PointerExt<[T]> {
    #[logic]
    fn as_ptr_logic(self) -> *const T;

    #[logic]
    fn len_logic(self) -> Int;

    #[logic(law)]
    #[ensures(self.as_ptr_logic() == other.as_ptr_logic() && self.len_logic() == other.len_logic() ==> self == other)]
    fn slice_ptr_ext(self, other: Self);
}

impl<T> SlicePointerExt<T> for *const [T] {
    /// Convert `*const [T]` to `*const T`.
    #[logic(open)]
    fn as_ptr_logic(self) -> *const T {
        self as *const T
    }

    /// Get the length metadata of the pointer.
    #[logic(open)]
    fn len_logic(self) -> Int {
        pearlite! { metadata_logic(self)@ }
    }

    /// Extensionality of slice pointers.
    #[trusted]
    #[logic(law)]
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
    #[erasure(<*const T>::add)]
    unsafe fn add_own(self, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> Self {
        self.add(offset)
    }
}

impl<T> PtrAddExt<T> for *mut T {
    #[trusted]
    #[requires(own.ptr().as_ptr_logic() == (self as *const T).offset_logic(offset@))]
    #[ensures(own.ptr().as_ptr_logic() == result as *const T)]
    #[erasure(<*mut T>::add)]
    unsafe fn add_own(self, offset: usize, own: Ghost<&PtrOwn<[T]>>) -> Self {
        self.add(offset)
    }
}

extern_spec! {
    impl<T: ?Sized> *const T {
        #[check(ghost)]
        #[ensures(result == self.addr_logic())]
        fn addr(self) -> usize;

        #[check(ghost)]
        #[ensures(result == self.is_null_logic())]
        fn is_null(self) -> bool;

        #[check(ghost)]
        #[erasure]
        #[ensures(result == self.is_aligned_logic())]
        fn is_aligned(self) -> bool
            where T: Sized,
        {
            self.is_aligned_to(std::mem::align_of::<T>())
        }

        #[check(ghost)]
        #[erasure]
        #[bitwise_proof]
        #[requires(align != 0usize && align & (align - 1usize) == 0usize)]
        #[ensures(result == self.is_aligned_to_logic(align))]
        fn is_aligned_to(self, align: usize) -> bool
        {
            if !align.is_power_of_two() {
                ::core::panic::panic_2021!("is_aligned_to: align is not a power-of-two");
            }
            self.addr() & (align - 1) == 0
        }
    }

    impl<T: ?Sized> *mut T {
        #[check(ghost)]
        #[ensures(result == self.addr_logic())]
        fn addr(self) -> usize;

        #[check(ghost)]
        #[ensures(result == self.is_null_logic())]
        fn is_null(self) -> bool;

        #[check(ghost)]
        #[erasure]
        #[ensures(result == self.is_aligned_logic())]
        fn is_aligned(self) -> bool
            where T: Sized,
        {
            self.is_aligned_to(std::mem::align_of::<T>())
        }

        #[check(ghost)]
        #[erasure]
        #[bitwise_proof]
        #[requires(align != 0usize && align & (align - 1usize) == 0usize)]
        #[ensures(result == self.is_aligned_to_logic(align))]
        fn is_aligned_to(self, align: usize) -> bool
        {
            if !align.is_power_of_two() {
                ::core::panic::panic_2021!("is_aligned_to: align is not a power-of-two");
            }
            self.addr() & (align - 1) == 0
        }
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
            #[check(ghost)]
            #[ensures(result.is_null_logic())]
            fn null<T>() -> *const T
            where
                T: std::ptr::Thin + ?Sized;

            #[check(ghost)]
            #[ensures(result.is_null_logic())]
            fn null_mut<T>() -> *mut T
            where
                T: std::ptr::Thin + ?Sized;

            #[check(ghost)]
            #[ensures(result == (p.addr_logic() == q.addr_logic()))]
            fn addr_eq<T, U>(p: *const T, q: *const U) -> bool
            where
                T: ?Sized, U: ?Sized;

            #[check(ghost)]
            #[ensures(result == metadata_logic(ptr))]
            fn metadata<T: ?Sized>(ptr: *const T) -> <T as Pointee>::Metadata;

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
