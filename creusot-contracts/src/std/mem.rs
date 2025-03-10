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
            #[ensures((^dest).is_default())]
            fn take<T: Default>(dest: &mut T) -> T {
                replace(dest, T::default())
            }

            #[pure]
            #[ensures(resolve(&_x))]
            fn drop<T>(_x: T) {}

            #[pure]
            #[ensures(resolve(&t))]
            fn forget<T>(t: T) {}
        }
    }
}
