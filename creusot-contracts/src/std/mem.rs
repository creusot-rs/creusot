use crate::{macros::*, std::default::Default};

extern_spec! {
    mod std {
        mod mem {
            #[ensures(^dest == src)]
            #[ensures(result == *dest)]
            fn replace<T>(dest: &mut T, src: T) -> T;

            #[ensures(^x == *y)]
            #[ensures(^y == *x)]
            fn swap<T>(x: &mut T, y: &mut T);

            #[ensures(result == *dest)]
            #[ensures((^dest).is_default())]
            fn take<T: Default>(dest: &mut T) -> T;
        }
    }
}
