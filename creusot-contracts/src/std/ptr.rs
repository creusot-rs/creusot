#[cfg(creusot)]
use crate::std::mem::{align_of_logic, size_of_logic, size_of_val_logic};
use crate::{
    ghost::perm::{Container, Perm},
    prelude::*,
};
use core::ptr::*;

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
#[logic(open, inline)]
#[intrinsic("metadata_matches")]
pub fn metadata_matches<T: ?Sized>(_value: T, _metadata: <T as Pointee>::Metadata) -> bool {
    dead
}

/// Definition of [`metadata_matches`] for slices.
#[allow(unused)]
#[logic]
#[intrinsic("metadata_matches_slice")]
fn metadata_matches_slice<T>(value: [T], len: usize) -> bool {
    pearlite! { value@.len() == len@ }
}

/// Definition of [`metadata_matches`] for string slices.
#[allow(unused)]
#[logic]
#[intrinsic("metadata_matches_str")]
fn metadata_matches_str(value: str, len: usize) -> bool {
    pearlite! { value@.to_bytes().len() == len@ }
}

/// Whether a pointer is aligned.
///
/// This is a logic version of [`<*const T>::is_aligned`][is_aligned],
/// but extended with an additional rule for `[U]`. We make use of this property
/// in [`ghost::perm::Perm<*const T>`] to define a more precise invariant for slice pointers.
///
/// - For `T: Sized`, specializes to [`is_aligned_logic_sized`].
/// - For `T = [U]`, specializes to [`is_aligned_logic_slice`].
/// - For `T = str`, specializes to `true`.
///
/// [is_aligned]: https://doc.rust-lang.org/std/primitive.pointer.html#method.is_aligned
#[allow(unused_variables)]
#[logic(open, inline)]
#[intrinsic("is_aligned_logic")]
pub fn is_aligned_logic<T: ?Sized>(ptr: *const T) -> bool {
    dead
}

/// Definition of [`is_aligned_logic`] for `T: Sized`.
#[allow(unused)]
#[logic]
#[intrinsic("is_aligned_logic_sized")]
fn is_aligned_logic_sized<T>(ptr: *const T) -> bool {
    ptr.is_aligned_to_logic(align_of_logic::<T>())
}

/// Definition of [`is_aligned_logic`] for `[T]`.
#[allow(unused)]
#[logic]
#[intrinsic("is_aligned_logic_slice")]
fn is_aligned_logic_slice<T>(ptr: *const [T]) -> bool {
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

/// Extension methods for `*const T` where `T: Sized`.
pub trait SizedPointerExt<T>: PointerExt<T> {
    /// Pointer offset in logic
    ///
    /// The current contract only describes the effect on `addr_logic` in the absence of overflow.
    #[logic]
    #[requires(self.addr_logic()@ + offset * size_of_logic::<T>() < usize::MAX@)]
    #[ensures(result.addr_logic()@ == self.addr_logic()@ + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> Self;

    /// Offset by zero is the identity
    #[logic(law)]
    #[ensures(self.offset_logic(0) == self)]
    fn offset_logic_zero(self);

    /// Offset is associative
    #[logic(law)]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int);

    /// Pointer subtraction
    ///
    /// Note: we don't have `ptr1 + (ptr2 - ptr1) == ptr2`, because pointer subtraction discards provenance.
    #[logic]
    fn sub_logic(self, rhs: Self) -> Int;

    #[logic(law)]
    #[ensures(self.sub_logic(self) == 0)]
    fn sub_logic_refl(self);

    #[logic(law)]
    #[ensures(self.offset_logic(offset).sub_logic(self) == offset)]
    fn sub_offset_logic(self, offset: Int);
}

impl<T> SizedPointerExt<T> for *const T {
    #[trusted]
    #[logic(opaque)]
    #[requires(self.addr_logic()@ + offset * size_of_logic::<T>() < usize::MAX@)]
    #[ensures(result.addr_logic()@ == self.addr_logic()@ + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> Self {
        dead
    }

    #[trusted]
    #[logic(law)]
    #[ensures(self.offset_logic(0) == self)]
    fn offset_logic_zero(self) {}

    #[trusted]
    #[logic(law)]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int) {}

    #[allow(unused)]
    #[trusted]
    #[logic(opaque)]
    fn sub_logic(self, rhs: Self) -> Int {
        dead
    }

    #[trusted]
    #[logic(law)]
    #[ensures(self.sub_logic(self) == 0)]
    fn sub_logic_refl(self) {}

    #[trusted]
    #[logic(law)]
    #[ensures(self.offset_logic(offset).sub_logic(self) == offset)]
    fn sub_offset_logic(self, offset: Int) {}
}

/// Extension methods for `*const [T]`
///
/// `thin` and `len_logic` are wrappers around `_ as *const T` and `metadata_logic`
/// that also pull in the `slice_ptr_ext` axiom when used.
pub trait SlicePointerExt<T>: PointerExt<[T]> {
    /// Remove metadata.
    #[logic]
    fn thin(self) -> *const T;

    /// Get the metadata.
    #[logic]
    fn len_logic(self) -> usize;

    /// Extensionality law.
    #[logic(law)]
    #[ensures(self.thin() == other.thin() && self.len_logic() == other.len_logic() ==> self == other)]
    fn slice_ptr_ext(self, other: Self);
}

impl<T> SlicePointerExt<T> for *const [T] {
    /// Convert `*const [T]` to `*const T`.
    #[logic(open, inline)]
    fn thin(self) -> *const T {
        self as *const T
    }

    /// Get the length metadata of the pointer.
    #[logic(open, inline)]
    fn len_logic(self) -> usize {
        pearlite! { metadata_logic(self) }
    }

    /// Extensionality of slice pointers.
    #[trusted]
    #[logic(law)]
    #[ensures(self.thin() == other.thin() && self.len_logic() == other.len_logic() ==> self == other)]
    fn slice_ptr_ext(self, other: Self) {}
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
        #[ensures(result == self as _)]
        fn cast<U>(self) -> *const U {
            self as _
        }

        #[check(terminates)]
        #[erasure]
        #[ensures(result == self.is_aligned_logic())]
        fn is_aligned(self) -> bool
            where T: Sized,
        {
            self.is_aligned_to(core::mem::align_of::<T>())
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
        #[ensures(result == self as _)]
        fn cast<U>(self) -> *mut U {
            self as _
        }

        #[check(terminates)]
        #[erasure]
        #[ensures(result == self.is_aligned_logic())]
        fn is_aligned(self) -> bool
            where T: Sized,
        {
            self.is_aligned_to(core::mem::align_of::<T>())
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
        #[ensures(result == metadata_logic(self))]
        fn len(self) -> usize;
    }

    impl<T> *mut [T] {
        #[ensures(result == metadata_logic(self))]
        fn len(self) -> usize;
    }

    mod core {
        mod ptr {
            #[check(ghost)]
            #[ensures(result.is_null_logic())]
            fn null<T>() -> *const T
            where
                T: core::ptr::Thin + ?Sized;

            #[check(ghost)]
            #[ensures(result.is_null_logic())]
            fn null_mut<T>() -> *mut T
            where
                T: core::ptr::Thin + ?Sized;

            #[check(ghost)]
            #[ensures(result == (p.addr_logic() == q.addr_logic()))]
            fn addr_eq<T, U>(p: *const T, q: *const U) -> bool
            where
                T: ?Sized, U: ?Sized;

            #[check(ghost)]
            #[ensures(result == metadata_logic(ptr))]
            fn metadata<T: ?Sized>(ptr: *const T) -> <T as Pointee>::Metadata;

            // Postulate `check(ghost)`.
            // It is used in a `#[trusted]` primitive in `peano`.
            #[check(ghost)]
            #[ensures(false)]
            unsafe fn read_volatile<T>(src: *const T) -> T;

            #[ensures(result as *const T == data && result.len_logic() == len)]
            fn slice_from_raw_parts<T>(data: *const T, len: usize) -> *const [T];

            #[ensures(result as *mut T == data && result.len_logic() == len)]
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

impl<T: ?Sized> Container for *const T {
    type Value = T;

    #[logic(open, inline)]
    fn is_disjoint(&self, self_val: &T, other: &Self, other_val: &T) -> bool {
        pearlite! {
            size_of_val_logic(*self_val) != 0 && size_of_val_logic(*other_val) != 0 ==>
            self.addr_logic() != other.addr_logic()
        }
    }
}

impl<T: ?Sized> Invariant for Perm<*const T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            !self.ward().is_null_logic()
                && self.ptr_is_aligned_opaque()
                && metadata_matches(*self.val(), metadata_logic(*self.ward()))
                // Allocations can never be larger than `isize` (source: https://doc.rust-lang.org/std/ptr/index.html#allocation)
                && size_of_val_logic(*self.val()) <= isize::MAX@
                // The allocation fits in the address space
                // (this is needed to verify (a `Perm` variant of) `<*const T>::add`, which checks this condition)
                && self.ward().addr_logic()@ + size_of_val_logic(*self.val()) <= usize::MAX@
                && inv(self.val())
        }
    }
}

impl<T: ?Sized> Perm<*const T> {
    /// Creates a new `Perm<*const T>` and associated `*const` by allocating a new memory
    /// cell initialized with `v`.
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(*result.1.ward() == result.0 && *result.1.val() == v)]
    pub fn new(v: T) -> (*mut T, Ghost<Box<Perm<*const T>>>)
    where
        T: Sized,
    {
        Self::from_box(Box::new(v))
    }

    /// Creates a ghost `Perm<*const T>` and associated `*const` from an existing [`Box`].
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(*result.1.ward() == result.0 && *result.1.val() == *val)]
    #[erasure(Box::into_raw)]
    pub fn from_box(val: Box<T>) -> (*mut T, Ghost<Box<Perm<*const T>>>) {
        (Box::into_raw(val), Ghost::conjure())
    }

    /// Decompose a shared reference into a raw pointer and a ghost `Perm<*const T>`.
    ///
    /// # Erasure
    ///
    /// This function erases to a raw reborrow of a reference.
    ///
    /// ```ignore
    /// Perm::from_ref(r)
    /// // erases to
    /// r as *const T  // or *mut T (both are allowed)
    /// ```
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(*result.1.ward() == result.0)]
    #[ensures(*result.1.val() == *r)]
    #[intrinsic("perm_from_ref")]
    pub fn from_ref(r: &T) -> (*const T, Ghost<&Perm<*const T>>) {
        (r, Ghost::conjure())
    }

    /// Decompose a mutable reference into a raw pointer and a ghost `Perm<*const T>`.
    ///
    /// # Erasure
    ///
    /// This function erases to a raw reborrow of a reference.
    ///
    /// ```ignore
    /// Perm::from_mut(r)
    /// // erases to
    /// r as *const T  // or *mut T (both are allowed)
    /// ```
    #[trusted]
    #[check(terminates)] // can overflow the number of available pointer adresses
    #[ensures(*result.1.ward() == result.0)]
    #[ensures(*result.1.val() == *r)]
    #[ensures(*(^result.1.inner_logic()).val() == ^r)]
    #[intrinsic("perm_from_mut")]
    pub fn from_mut(r: &mut T) -> (*mut T, Ghost<&mut Perm<*const T>>) {
        (r, Ghost::conjure())
    }

    /// Immutably borrows the underlying `T`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as a direct dereference: `&*ptr`.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](Perm).
    ///
    /// # Erasure
    ///
    /// This function erases to a cast from raw pointer to shared reference.
    ///
    /// ```ignore
    /// Perm::as_ref(ptr, own)
    /// // erases to
    /// & *ptr
    /// ```
    #[trusted]
    #[check(terminates)]
    #[requires(ptr == *own.ward())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    #[intrinsic("perm_as_ref")]
    pub unsafe fn as_ref(ptr: *const T, own: Ghost<&Perm<*const T>>) -> &T {
        unsafe { &*ptr }
    }

    /// Mutably borrows the underlying `T`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as a direct dereference: `&mut *ptr`.
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](Perm).
    ///
    /// # Erasure
    ///
    /// This function erases to a cast from raw pointer to mutable reference.
    ///
    /// ```ignore
    /// Perm::as_mut(ptr, own)
    /// // erases to
    /// &mut *ptr
    /// ```
    #[trusted]
    #[check(terminates)]
    #[allow(unused_variables)]
    #[requires(ptr as *const T == *own.ward())]
    #[ensures(*result == *own.val())]
    #[ensures((^own).ward() == own.ward())]
    #[ensures(*(^own).val() == ^result)]
    #[intrinsic("perm_as_mut")]
    pub unsafe fn as_mut(ptr: *mut T, own: Ghost<&mut Perm<*const T>>) -> &mut T {
        unsafe { &mut *ptr }
    }

    /// Transfers ownership of `own` back into a [`Box`].
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as [`Box::from_raw`].
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](Perm).
    #[trusted]
    #[check(terminates)]
    #[requires(ptr as *const T == *own.ward())]
    #[ensures(*result == *own.val())]
    #[allow(unused_variables)]
    #[erasure(Box::from_raw)]
    pub unsafe fn to_box(ptr: *mut T, own: Ghost<Box<Perm<*const T>>>) -> Box<T> {
        unsafe { Box::from_raw(ptr) }
    }

    /// Deallocates the memory pointed by `ptr`.
    ///
    /// # Safety
    ///
    /// Safety requirements are the same as [`Box::from_raw`].
    ///
    /// Creusot will check that all calls to this function are indeed safe: see the
    /// [type documentation](Perm).
    #[check(terminates)]
    #[requires(ptr as *const T == *own.ward())]
    pub unsafe fn drop(ptr: *mut T, own: Ghost<Box<Perm<*const T>>>) {
        let _ = unsafe { Self::to_box(ptr, own) };
    }

    /// The pointer of a `Perm<*const T>` is always aligned.
    #[check(ghost)]
    #[ensures(self.ward().is_aligned_logic())]
    pub fn ptr_is_aligned_lemma(&self) {}

    /// Opaque wrapper around [`std::ptr::is_aligned_logic`].
    /// We use this to hide alignment logic by default in `invariant` because it confuses SMT solvers sometimes.
    /// The underlying property is exposed by [`Perm::ptr_is_aligned_lemma`].
    #[logic(open(self))]
    pub fn ptr_is_aligned_opaque(self) -> bool {
        self.ward().is_aligned_logic()
    }
}
