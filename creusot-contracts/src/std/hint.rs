use crate::*;

extern_spec! {
    mod std {
        mod hint {
            #[safety(ghost)]
            #[requires(cond)]
            unsafe fn assert_unchecked(cond: bool) {}

            #[safety(ghost)]
            #[ensures(result == dummy)]
            fn black_box<T>(dummy: T) -> T {
                dummy
            }

            #[safety(ghost)]
            #[requires(true)]
            #[ensures(true)]
            fn spin_loop() {}

            #[safety(ghost)]
            #[requires(false)]
            unsafe fn unreachable_unchecked() -> ! {
                unreachable!()
            }

            #[cfg(feature = "nightly")]
            #[safety(ghost)]
            #[ensures(result == value)]
            fn must_use<T>(value: T) -> T {
                value
            }
        }
    }
}
