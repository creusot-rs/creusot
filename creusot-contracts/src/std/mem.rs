use crate::*;
pub use ::std::mem::*;

extern_spec! {
    mod std {
        mod mem {
            #[pure]
            #[ensures(^dest == src)]
            #[ensures(result == *dest)]
            fn replace<T>(dest: &mut T, src: T) -> T {
                let mut src = src;
                swap(dest, &mut src);
                src
            }

            #[pure]
            #[ensures(^x == *y)]
            #[ensures(^y == *x)]
            fn swap<T>(x: &mut T, y: &mut T);

            #[ensures(result == *dest)]
            #[ensures(T::default.postcondition((), ^dest))]
            fn take<T: Default>(dest: &mut T) -> T {
                replace(dest, T::default())
            }

            #[pure]
            #[ensures(resolve(&_x))]
            fn drop<T>(_x: T) {}

            #[pure]
            #[ensures(resolve(&t))]
            fn forget<T>(t: T) {}

            #[pure]
            #[ensures(result@ == size_of_logic::<T>())]
            fn size_of<T>() -> usize;
        }
    }
}

/// `size_of` as a logic `Int` value.
///
/// This is a special function with a compiler-provided definition.
#[logic]
#[trusted]
#[rustc_diagnostic_item = "size_of_logic"]
#[ensures(0 <= result)]
pub fn size_of_logic<T>() -> Int {
    dead
}
