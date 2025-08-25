#[cfg(creusot)]
use crate::std::mem::{align_of_logic, size_of_logic, size_of_val_logic};
use crate::{
    ghost::perm::{Container, Perm},
    prelude::*,
};
use core::marker::PhantomData;
#[cfg(creusot)]
use core::ptr::Pointee;

#[cfg(not(feature = "std"))]
use alloc::boxed::Box;

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

/// Extension trait for pointers
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

// Implemented using the impl for `*const T`
impl<T> SizedPointerExt<T> for *mut T {
    #[logic(open, inline)]
    #[requires(self.addr_logic()@ + offset * size_of_logic::<T>() < usize::MAX@)]
    #[ensures(result.addr_logic()@ == self.addr_logic()@ + offset * size_of_logic::<T>())]
    fn offset_logic(self, offset: Int) -> Self {
        pearlite! { (self as *const T).offset_logic(offset) as *mut T }
    }

    #[logic(law)]
    #[ensures(self.offset_logic(0) == self)]
    fn offset_logic_zero(self) {}

    #[logic(law)]
    #[ensures(self.offset_logic(offset1).offset_logic(offset2) == self.offset_logic(offset1 + offset2))]
    fn offset_logic_assoc(self, offset1: Int, offset2: Int) {}

    #[logic(open, inline)]
    fn sub_logic(self, rhs: Self) -> Int {
        pearlite! { (self as *const T).sub_logic(rhs as *const T) }
    }

    #[logic(law)]
    #[ensures(self.sub_logic(self) == 0)]
    fn sub_logic_refl(self) {}

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

impl<T> SlicePointerExt<T> for *mut [T] {
    /// Convert `*const [T]` to `*const T`.
    #[logic(open, inline)]
    fn thin(self) -> *const T {
        self as *const T
    }

    /// Get the length metadata of the pointer.
    #[logic(open, inline)]
    fn len_logic(self) -> usize {
        pearlite! { metadata_logic(self as *const [T]) }
    }

    /// Extensionality of slice pointers.
    #[logic(law)]
    #[ensures(self.thin() == other.thin() && self.len_logic() == other.len_logic() ==> self == other)]
    fn slice_ptr_ext(self, other: Self) {
        (self as *const [T]).slice_ptr_ext(other as *const [T])
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
                && metadata_matches(*self.val(), metadata_logic(*self.ward()))
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
    /// r as *const T
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
    /// r as *mut T
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
}

/// # Permissions for slice pointers
///
/// Core methods:
///
/// - To split a `&Perm<*const [T]>`: [`split_at`](Perm::split_at), [`split_at_mut`](Perm::split_at_mut).
/// - To index a `&Perm<*const [T]>` into `&Perm<*const T>`: [`elements`](Perm::elements), [`elements_mut`](Perm::elements_mut).
/// - To extract a [`PtrLive<T>`][PtrLive] (evidence used by pointer arithmetic): [`live`](Perm::live), [`live_mut`](LiveMut::live_mut).
impl<T> Perm<*const [T]> {
    /// The number of elements in the slice.
    #[logic(open, inline)]
    pub fn len(self) -> Int {
        pearlite! { self.val()@.len() }
    }

    /// Split a `&Perm<*const [T]>` into two subslices of lengths `index` and `self.len() - index`.
    #[trusted]
    #[check(ghost)]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ward().thin() == result.0.ward().thin())]
    #[ensures(self.ward().thin().offset_logic(index) == result.1.ward().thin())]
    #[ensures(self.val()@[..index] == result.0.val()@)]
    #[ensures(self.val()@[index..] == result.1.val()@)]
    pub fn split_at(&self, index: Int) -> (&Self, &Self) {
        let _ = index;
        panic!("called ghost function in normal code")
    }

    /// Split a `&mut Perm<*const [T]>` into two subslices of lengths `index` and `self.len() - index`.
    #[trusted]
    #[check(ghost)]
    #[requires(0 <= index && index <= self.len())]
    #[ensures(self.ward().thin() == result.0.ward().thin())]
    #[ensures(self.ward().thin().offset_logic(index) == result.1.ward().thin())]
    #[ensures(self.val()@[..index] == result.0.val()@)]
    #[ensures(self.val()@[index..] == result.1.val()@)]
    #[ensures((^self).ward() == self.ward())]
    #[ensures((^result.0).val()@.len() == index)]
    #[ensures((^self).val()@ == (^result.0).val()@.concat((^result.1).val()@))]
    pub fn split_at_mut(&mut self, index: Int) -> (&mut Perm<*const [T]>, &mut Perm<*const [T]>) {
        let _ = index;
        panic!("called ghost function in normal code")
    }

    /// Split `&Perm<*const [T]>` into a sequence of `&Perm<*const T>` for each element.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<i> 0 <= i && i < self.len()
        ==> *result[i].ward() == self.ward().thin().offset_logic(i)
        && *result[i].val() == self.val()@[i])]
    pub fn elements(&self) -> Seq<&Perm<*const T>> {
        panic!("called ghost function in normal code")
    }

    /// Split `&mut Perm<*const [T]>` into a sequence of `&mut Perm<*const T>` for each element.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.len() == self.len())]
    #[ensures(forall<i> 0 <= i && i < self.len()
        ==> *result[i].ward() == self.ward().thin().offset_logic(i)
        && *result[i].val() == self.val()@[i])]
    #[ensures((^self).ward() == self.ward())]
    #[ensures(forall<i> 0 <= i && i < self.len() ==> *(^result[i]).val() == (^self).val()@[i])]
    pub fn elements_mut(&mut self) -> Seq<&mut Perm<*const T>> {
        panic!("called ghost function in normal code")
    }

    /// Index a `&Perm<*const [T]>` into a `&Perm<*const T>`.
    #[check(ghost)]
    #[requires(0 <= index && index < self.len())]
    #[ensures(*result.ward() == self.ward().thin().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    pub fn index(&self, index: Int) -> &Perm<*const T> {
        let mut r = self.elements();
        r.split_off_ghost(index).pop_front_ghost().unwrap()
    }

    /// Index a `&mut Perm<*const [T]>` into a `&mut Perm<*const T>`.
    #[check(ghost)]
    #[requires(0 <= index && index < self.len())]
    #[ensures(*result.ward() == self.ward().thin().offset_logic(index))]
    #[ensures(*result.val() == self.val()@[index])]
    #[ensures((^self).ward() == self.ward())]
    #[ensures(*(^result).val() == (^self).val()@[index])]
    #[ensures(forall<k: Int> 0 <= k && k < self.len() && k != index ==> (^self).val()@[k] == self.val()@[k])]
    pub fn index_mut(&mut self, index: Int) -> &mut Perm<*const T> {
        let mut r = self.elements_mut();
        proof_assert! { forall<k> index < k && k < r.len() ==> r[k].val() == r[index..].tail()[k-index-1].val() };
        let _r = snapshot! { r };
        let result = r.split_off_ghost(index).pop_front_ghost().unwrap();
        proof_assert! { forall<i> 0 <= i && i < index ==> r[i] == _r[i] }; // Unfolding of ensures of split_off_ghost r == _r[..index]
        result
    }

    /// Extract `PtrLive<'a, T>` from `&'a Perm<*const [T]>`.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.ward() == self.ward().thin())]
    #[ensures(result.len()@ == self.len())]
    pub fn live(&self) -> PtrLive<'_, T> {
        panic!("called ghost function in normal code")
    }
}

/// Extension trait with the `live_mut` method
///
/// Naively, we wanted `live_mut(&'b &'a mut self) -> PtrLive<'a, T>` where `Self = Perm<*const [T]>`,
/// but `self` being a double borrow is illegal.
pub trait LiveMut<'a, T> {
    /// Extract `PtrLive<'a, T>` from `&'a mut Perm<*const [T]>`.
    fn live_mut<'b>(&'b self) -> PtrLive<'a, T>;
}

impl<'a, T> LiveMut<'a, T> for &'a mut Perm<*const [T]> {
    /// Extract `PtrLive<'a, T>` from `&'a mut Perm<*const [T]>`.
    #[trusted]
    #[check(ghost)]
    #[ensures(result.ward() == self.ward().thin())]
    #[ensures(result.len()@ == self.len())]
    fn live_mut<'b>(&'b self) -> PtrLive<'a, T> {
        panic!("called ghost function in normal code")
    }
}

/// Evidence that a range of memory is alive.
///
/// This evidence enables taking pointer offsets (see [`PtrAddExt`])
/// without ownership of that range of memory (*i.e.*, not using [`Perm`]).
///
/// Its lifetime is bounded by some `&Perm<*const [T]>` (via `Perm::live`
/// or `Perm::live_mut`) so it can't outlive the associated allocation.
#[opaque]
pub struct PtrLive<'a, T>(PhantomData<&'a T>);

impl<T> Clone for PtrLive<'_, T> {
    #[trusted]
    #[check(ghost)]
    #[ensures(result == *self)]
    fn clone(&self) -> Self {
        panic!("called ghost function in normal code")
    }
}

impl<T> Copy for PtrLive<'_, T> {}

impl<T> Invariant for PtrLive<'_, T> {
    #[logic(open, prophetic)]
    fn invariant(self) -> bool {
        pearlite! {
            // Allocations can never be larger than `isize` bytes
            // (source: <https://doc.rust-lang.org/std/ptr/index.html#allocation>)
            self.len()@ * size_of_logic::<T>() <= isize::MAX@
            // The allocation fits in the address space
            // (for example, this is needed to verify (a `Perm`-aware variant of)
            // `<*const T>::add`, which checks this condition)
            && self.ward().addr_logic()@ + self.len()@ * size_of_logic::<T>() <= usize::MAX@
            // The pointer of a `Perm` is always aligned.
            && self.ward().is_aligned_logic()
        }
    }
}

impl<T> PtrLive<'_, T> {
    /// Base pointer, start of the range
    #[trusted]
    #[logic(opaque)]
    pub fn ward(self) -> *const T {
        dead
    }

    /// The number of elements (of type `T`) in the range.
    ///
    /// The length in bytes is thus `self.len()@ * size_of_logic::<T>()`.
    #[trusted]
    #[logic(opaque)]
    pub fn len(self) -> usize {
        dead
    }

    /// Range inclusion.
    ///
    /// The live range `self.ward()..=(self.ward() + self.len())` contains
    /// the range `ptr..=(ptr + len)`.
    ///
    /// Note that the out-of-bounds pointer `self.ward() + self.len()`
    /// is included.
    /// The provenance of `ptr` must be the same as `self.ward()`.
    #[logic(open, inline)]
    pub fn contains_range(self, ptr: *const T, len: Int) -> bool {
        pearlite! {
            let offset = ptr.sub_logic(self.ward());
            // This checks that the provenance is the same.
            ptr == self.ward().offset_logic(offset)
            && 0 <= offset && offset <= self.len()@
            && 0 <= offset + len && offset + len <= self.len()@
        }
    }
}

/// Pointer offsets with [`PtrLive`] permissions.
///
/// This trait provides wrappers around the offset functions:
///
/// - [`<*const T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add)
/// - [`<*const T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset)
/// - [`<*mut T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add-1)
/// - [`<*mut T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset-1)
///
/// with ghost permission tokens (`PtrLive`) that allow proving their safety conditions.
///
/// # Safety
///
/// Source: <https://doc.rust-lang.org/core/intrinsics/fn.offset.html>
///
/// > If the computed offset is non-zero, then both the starting and resulting pointer must be either in bounds or at the end of an allocation.
/// > If either pointer is out of bounds or arithmetic overflow occurs then this operation is undefined behavior.
///
/// The preconditions ensure that the `live` witness contains the range between `dst` and `dst + offset`,
/// which prevents out-of-bounds access and overflow.
pub trait PtrAddExt<'a, T> {
    /// Implementations refine this with a non-trivial precondition.
    #[requires(false)]
    unsafe fn add_live(self, offset: usize, live: Ghost<PtrLive<'a, T>>) -> Self;

    /// Implementations refine this with a non-trivial precondition.
    #[requires(false)]
    unsafe fn offset_live(self, offset: isize, live: Ghost<PtrLive<'a, T>>) -> Self;
}

impl<'a, T> PtrAddExt<'a, T> for *const T {
    /// Permission-aware wrapper around [`<*const T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add)
    #[trusted]
    #[erasure(<*const T>::add)]
    #[requires(live.contains_range(self, offset@))]
    #[ensures(result == self.offset_logic(offset@))]
    unsafe fn add_live(self, offset: usize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        unsafe { self.add(offset) }
    }

    /// Permission-aware wrapper around [`<*const T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset)
    #[trusted]
    #[erasure(<*const T>::offset)]
    #[requires(live.contains_range(self, offset@))]
    #[ensures(result == self.offset_logic(offset@))]
    unsafe fn offset_live(self, offset: isize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        unsafe { self.offset(offset) }
    }
}

impl<'a, T> PtrAddExt<'a, T> for *mut T {
    /// Permission-aware wrapper around [`<*mut T>::add`](https://doc.rust-lang.org/core/primitive.pointer.html#method.add-1)
    #[trusted]
    #[erasure(<*mut T>::add)]
    #[requires(live.contains_range(self, offset@))]
    #[ensures(result == self.offset_logic(offset@))]
    unsafe fn add_live(self, offset: usize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        unsafe { self.add(offset) }
    }

    /// Permission-aware wrapper around [`<*mut T>::offset`](https://doc.rust-lang.org/core/primitive.pointer.html#method.offset-1)
    #[trusted]
    #[erasure(<*mut T>::offset)]
    #[requires(live.contains_range(self, offset@))]
    #[ensures(result == self.offset_logic(offset@))]
    unsafe fn offset_live(self, offset: isize, live: Ghost<PtrLive<'a, T>>) -> Self {
        let _ = live;
        unsafe { self.offset(offset) }
    }
}
