use crate::*;
use ::core::fmt;
#[cfg(feature = "nightly")]
pub use ::core::panicking::*;
use ::std::any::Any;

extern_spec! {
    mod core {
        mod panicking {
            #[check(ghost)]
            #[requires(false)]
            fn panic(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn panic_display<T: fmt::Display>(x: &T) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn panic_fmt(fmt: fmt::Arguments<'_>) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn panic_nounwind(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn panic_nounwind_fmt(fmt: fmt::Arguments<'_>, force_no_backtrace: bool) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn panic_nounwind_nobacktrace(expr: &'static str) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn unreachable_display<T: fmt::Display>(x: &T) -> !;

            #[check(ghost)]
            #[requires(false)]
            fn assert_failed<T, U>(kind: AssertKind, left: &T, right: &U, args: Option<fmt::Arguments<'_>>) -> !
            where
                T: fmt::Debug + ?Sized,
                U: fmt::Debug + ?Sized;

        }
    }

    mod std {
        mod rt {
            #[check(ghost)]
            #[requires(false)]
            fn begin_panic<M: Any + Send>(msg: M) -> !;
        }
    }
}
