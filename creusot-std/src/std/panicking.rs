use crate::prelude::*;
#[cfg(all(creusot, feature = "std"))]
use core::any::Any;
#[cfg(creusot)]
use core::{
    fmt::{Arguments, Debug, Display},
    panicking::AssertKind,
};

extern_spec! {
    mod core {
        mod panicking {
            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_display<T: Display>(x: &T) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_fmt(fmt: Arguments<'_>) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_nounwind(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_nounwind_fmt(fmt: Arguments<'_>, force_no_backtrace: bool) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_nounwind_nobacktrace(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn unreachable_display<T: Display>(x: &T) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn assert_failed<T: Debug + ?Sized, U: Debug + ?Sized>(
                kind: AssertKind,
                left: &T,
                right: &U,
                args: Option<Arguments<'_>>
            ) -> !;
        }
    }
}

#[cfg(feature = "std")]
extern_spec! {
    mod std {
        mod rt {
            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn begin_panic<M: Any + Send>(msg: M) -> !;
        }
    }
}
