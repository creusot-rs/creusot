use crate::*;
pub use ::std::mem::*;

extern_spec! {
    mod std {
        mod mem {
            #[pure]
            #[ensures(^dest == src)]
            #[ensures(result == *dest)]
            fn replace<T>(dest: &mut T, src: T) -> T;

            #[pure]
            #[ensures(^x == *y)]
            #[ensures(^y == *x)]
            fn swap<T>(x: &mut T, y: &mut T);

            #[ensures(result == *dest)]
            #[ensures((^dest).is_default())]
            fn take<T: Default>(dest: &mut T) -> T;
        }
    }
}
