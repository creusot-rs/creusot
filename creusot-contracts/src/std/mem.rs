use crate as creusot_contracts;
use crate::std::default::Default;
use creusot_contracts_proc::*;

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
            #[ensures(^dest == T::default_log())]
            fn take<T: Default>(dest: &mut T) -> T;
        }
    }
}
