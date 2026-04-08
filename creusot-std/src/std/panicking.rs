use crate::prelude::*;
#[cfg(all(creusot, feature = "std"))]
use core::any::Any;
#[cfg(creusot)]
use core::{fmt, panicking::AssertKind};

extern_spec! {
    mod core {
        mod panicking {
            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_display<T: fmt::Display>(x: &T) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_fmt(fmt: fmt::Arguments<'_>) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_nounwind(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_nounwind_fmt(fmt: fmt::Arguments<'_>, force_no_backtrace: bool) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn panic_nounwind_nobacktrace(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn unreachable_display<T: fmt::Display>(x: &T) -> !;

            #[check(ghost)]
            #[requires(|mode| !mode.nopanic())]
            fn assert_failed<T, U>(kind: AssertKind, left: &T, right: &U, args: Option<fmt::Arguments<'_>>) -> !
            where
                T: fmt::Debug + ?Sized,
                U: fmt::Debug + ?Sized;

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
