use crate::*;
pub use ::std::mem::*;

extern_spec! {
    mod std {
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

            #[check(ghost)]
            #[ensures(result@ == size_of_logic::<T>())]
            fn size_of<T>() -> usize;

            // Note: you may be tempted to add `result@ <= isize::MAX@`.
            // Indeed, allocation size is bounded; source: https://doc.rust-lang.org/std/ptr/index.html#allocation
            // But this is not true in ghost code. Counterexample:
            //
            // ```
            // #[ensures(false)]
            // pub fn bad() {
            //     ghost! {
            //         let x = [0usize; usize::MAX];
            //         let _ = ::std::mem::size_of_val(&x);
            //     };
            // }
            // ```
            #[check(ghost)]
            #[ensures(result@ == size_of_val_logic::<T>(*val))]
            fn size_of_val<T: ?Sized>(val: &T) -> usize;

            #[check(ghost)]
            #[ensures(result == align_of_logic::<T>())]
            fn align_of<T>() -> usize;
        }
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
