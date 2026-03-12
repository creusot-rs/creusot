use crate::prelude::*;
use core::mem::*;
#[cfg(creusot)]
use std::marker::DiscriminantKind;

impl<T> View for MaybeUninit<T> {
    type ViewTy = Option<T>;

    #[logic(opaque)]
    fn view(self) -> Option<T> {
        dead
    }
}

extern_spec! {
    mod core {
        mod mem {
            #[check(ghost)]
            #[ensures(^dest == src)]
            #[ensures(result == *dest)]
            fn replace<T>(dest: &mut T, src: T) -> T {
                let mut src = src;
                swap(dest, &mut src);
                src
            }

            #[check(ghost)]
            #[ensures(^x == *y)]
            #[ensures(^y == *x)]
            fn swap<T>(x: &mut T, y: &mut T);

            #[ensures(result == *dest)]
            #[ensures(T::default.postcondition((), ^dest))]
            fn take<T: Default>(dest: &mut T) -> T {
                replace(dest, T::default())
            }

            #[check(ghost)]
            #[ensures(resolve(t))]
            fn drop<T>(t: T) {}

            #[check(ghost)]
            #[ensures(resolve(t))]
            fn forget<T>(t: T) {}

            // This is not `#[check(ghost)]` because `size_of` overflows are only caught at codegen time
            // which ghost code doesn't reach.
            #[check(terminates)]
            #[ensures(result@ == size_of_logic::<T>())]
            fn size_of<T>() -> usize;

            // This is not `#[check(ghost)]` because `size_of_val` overflows are only caught at codegen time
            // which ghost code doesn't reach.
            #[check(terminates)]
            #[ensures(result@ == size_of_val_logic::<T>(*val))]
            fn size_of_val<T: ?Sized>(val: &T) -> usize;

            // This is not `#[check(ghost)]` because `align_of` overflows are only caught at codegen time
            // which ghost code doesn't reach.
            //
            // Alignment values may range from 1 to 2^29
            // ([source](https://doc.rust-lang.org/reference/type-layout.html#r-layout.repr.alignment.constraint-alignment)),
            // which may overflow on 16-bit archs.
            #[check(terminates)]
            #[ensures(result == align_of_logic::<T>())]
            fn align_of<T>() -> usize;

            #[check(ghost)]
            #[ensures(result == discriminant_logic(*v))]
            fn discriminant<T>(v: &T) -> Discriminant<T>;
        }
    }

    impl<T> MaybeUninit<T> {
        #[ensures(result@ == Some(val))]
        #[check(ghost)]
        fn new(val: T) -> Self;

        #[ensures(result@ == None)]
        #[check(ghost)]
        fn uninit() -> Self;

        #[requires(self@ == None)] // NOTE: we could allow calling this on an initialized `MaybeUninit`, but this would leak the contents.
        #[ensures(*result == val)]
        #[ensures((^self)@ == Some(^result))]
        #[check(ghost)]
        fn write(&mut self, val: T) -> &mut T;

        #[requires(self@ != None)]
        #[ensures(self@ == Some(result))]
        #[check(ghost)]
        const unsafe fn assume_init(self) -> T;

        #[requires(self@ != None)]
        #[ensures((^self)@ == None)]
        #[check(ghost)]
        unsafe fn assume_init_drop(&mut self);

        #[requires(self@ != None)]
        #[ensures(self@ == Some(*result))]
        #[check(ghost)]
        const unsafe fn assume_init_ref(&self) -> &T;

        #[requires(self@ != None)]
        #[ensures((*self)@ == Some(*result) && (^self)@ == Some(^result))]
        #[check(ghost)]
        const unsafe fn assume_init_mut(&mut self) -> &mut T;
    }
}

/// [`size_of`] as a logic `Int` value.
///
/// The definition of `size_of_logic` guarantees at least the following,
/// based on the documentation of [`size_of`]:
///
/// - `()`, `bool`, `char`, primitive integers and floats are known constants.
/// - For `T: Sized`, the pointer and reference types `*const T`, `*mut T`,
///   `&T`, `&mut T`, `Box<T>`, `Option<&T>`, `Option<&mut T>`, and
///   `Option<Box<T>>` have the same size as `usize`.
/// - `[T; N]` has size `N * size_of_logic::<T>()`.
///
/// `size_of_logic` for `repr(C)` types is not yet implemented.
///
/// See also [the Rust Reference section on Type Layout][RRTL].
///
/// Note that the value of `size_of`/`size_of_logic` may depend on the version of rustc, notably
/// for ADTs with the default representation `repr(Rust)`.
///
/// [`size_of`]: https://doc.rust-lang.org/std/mem/fn.size_of.html
/// [RRTL]: https://doc.rust-lang.org/stable/reference/type-layout.html
#[trusted]
#[logic(open, inline)]
#[intrinsic("size_of_logic")]
#[ensures(0 <= result)]
pub fn size_of_logic<T>() -> Int {
    dead
}

/// [`size_of_val`] as a logic `Int` value.
#[trusted]
#[logic(open, inline)]
#[intrinsic("size_of_val_logic")]
#[ensures(0 <= result)]
pub fn size_of_val_logic<T: ?Sized>(val: T) -> Int {
    dead
}

#[allow(unused)]
#[logic]
#[intrinsic("size_of_val_logic_sized")]
fn size_of_val_logic_sized<T>(_val: T) -> Int {
    size_of_logic::<T>()
}

#[allow(unused)]
#[logic]
#[intrinsic("size_of_val_logic_slice")]
fn size_of_val_logic_slice<T>(val: [T]) -> Int {
    pearlite! { size_of_logic::<T>() * val@.len() }
}

#[allow(unused)]
#[logic]
#[intrinsic("size_of_val_logic_str")]
fn size_of_val_logic_str(val: str) -> Int {
    pearlite! { val@.to_bytes().len() }
}

/// [`align_of`] as a logic `Int` value.
///
/// [`align_of`]: https://doc.rust-lang.org/std/mem/fn.align_of.html
#[trusted]
#[logic(open, inline)]
#[intrinsic("align_of_logic")]
#[ensures(0usize != result && result & (result - 1usize) == 0usize)]
#[ensures(size_of_logic::<T>() % result@ == 0)]
pub fn align_of_logic<T>() -> usize {
    dead
}

/// Logic version of [`std::mem::discriminant`]
#[logic(open, inline)]
pub fn discriminant_logic<T>(v: T) -> Discriminant<T> {
    pearlite! { T::into_discriminant(strong_discriminant(v)) }
}

/// Logic version of [`std::intrinsics::discriminant_value`]
#[logic(open, inline)]
pub fn discriminant_value_logic<T>(v: T) -> <T as DiscriminantKind>::Discriminant {
    pearlite! { T::into_discriminant_value(strong_discriminant(v)) }
}

/// Map each variant of the enum `T` to an integer, in order of declaration starting from 0.
///
/// Undefined if `T` is not an enum.
///
/// This is a "strongly specified" discriminant, as opposed to the "weakly specified"
/// [`std::mem::discriminant`], for which the precise value of the discriminant of each
/// variant is not specified.
///
/// We bridge the gap by postulating an injection [`into_discriminant`] from this
/// "strongly specified" discriminant to the "weakly specified" one.
// #[logic(open, inline)] // TODO
#[logic(opaque)]
#[intrinsic("strong_discriminant")]
pub fn strong_discriminant<T>(v: T) -> usize {
    let _ = v;
    dead
}

/// Number of variants of the enum `T`.
///
/// Undefined if `T` is not an enum.
// #[logic(open, inline)] // TODO
#[logic(opaque)]
#[intrinsic("discriminant_count")]
pub fn variant_count<T>() -> usize {
    dead
}

/// Injections between discriminants.
///
/// This trait allows auto-loading the injectivity laws whenever these functions are used.
pub trait IntoDiscriminant: Sized {
    /// Map the output of [`strong_discriminant_logic`] to the corresponding output of [`std::mem::discriminant`].
    #[logic]
    fn into_discriminant(v: usize) -> Discriminant<Self>;

    /// Map the output of [`strong_discriminant_logic`] to the corresponding output of [`std::intrinsics::discriminant_value`].
    #[logic]
    fn into_discriminant_value(v: usize) -> <Self as DiscriminantKind>::Discriminant;

    #[logic(law)]
    #[ensures(forall<v1, v2> v1 < variant_count::<Self>() && v2 < variant_count::<Self>()
        ==> Self::into_discriminant(v1) == Self::into_discriminant(v2) ==> v1 == v2)]
    fn into_discriminant_injective();

    #[trusted]
    #[logic(law)]
    #[ensures(forall<v1, v2> v1 < variant_count::<Self>() && v2 < variant_count::<Self>()
        ==> Self::into_discriminant_value(v1) == Self::into_discriminant_value(v2) ==> v1 == v2)]
    fn into_discriminant_value_injective();
}

impl<T> IntoDiscriminant for T {
    #[logic(opaque)]
    fn into_discriminant(v: usize) -> Discriminant<T> {
        let _ = v;
        dead
    }

    #[logic(opaque)]
    fn into_discriminant_value(v: usize) -> <T as DiscriminantKind>::Discriminant {
        let _ = v;
        dead
    }

    #[trusted]
    #[logic(law)]
    #[ensures(forall<v1, v2> v1 < variant_count::<Self>() && v2 < variant_count::<Self>()
        ==> Self::into_discriminant(v1) == Self::into_discriminant(v2) ==> v1 == v2)]
    fn into_discriminant_injective() {}

    #[trusted]
    #[logic(law)]
    #[ensures(forall<v1, v2> v1 < variant_count::<Self>() && v2 < variant_count::<Self>()
        ==> Self::into_discriminant_value(v1) == Self::into_discriminant_value(v2) ==> v1 == v2)]
    fn into_discriminant_value_injective() {}
}

impl<T> DeepModel for Discriminant<T> {
    type DeepModelTy = Self;

    #[logic(open, inline)]
    fn deep_model(self) -> Self::DeepModelTy {
        self
    }
}
