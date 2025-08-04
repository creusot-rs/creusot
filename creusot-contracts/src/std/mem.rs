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
#[logic]
#[open]
#[rustc_diagnostic_item = "size_of_logic"]
#[ensures(0 <= result)]
pub fn size_of_logic<T>() -> Int {
    dead
}
