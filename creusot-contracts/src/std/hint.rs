use crate::*;

extern_spec! {
    mod std {
        mod hint {
            #[pure]
            #[requires(cond)]
            unsafe fn assert_unchecked(cond: bool) {}

            #[pure]
            #[ensures(result == dummy)]
            fn black_box<T>(dummy: T) -> T {
                dummy
            }

            #[pure]
            #[requires(true)]
            #[ensures(true)]
            fn spin_loop() {}

            #[pure]
            #[requires(false)]
            unsafe fn unreachable_unchecked() -> ! {
                unreachable!()
            }

            #[cfg(feature = "nightly")]
            #[pure]
            #[ensures(result == value)]
            fn must_use<T>(value: T) -> T {
                value
            }
        }
    }
}
