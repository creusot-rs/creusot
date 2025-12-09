use crate::prelude::*;

extern_spec! {
    mod core {
        mod hint {
            #[check(ghost)]
            #[requires(cond)]
            unsafe fn assert_unchecked(cond: bool) {}

            #[check(ghost)]
            #[ensures(result == dummy)]
            fn black_box<T>(dummy: T) -> T {
                dummy
            }

            #[check(ghost)]
            #[requires(true)]
            #[ensures(true)]
            fn spin_loop() {}

            #[check(ghost)]
            #[requires(false)]
            unsafe fn unreachable_unchecked() -> ! {
                unreachable!()
            }

            #[cfg(feature = "nightly")]
            #[check(ghost)]
            #[ensures(result == value)]
            fn must_use<T>(value: T) -> T {
                value
            }
        }
    }
}
