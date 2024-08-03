use crate::*;
use ::core::fmt;
pub use ::core::panicking::*;
use ::std::any::Any;

extern_spec! {
    mod core {
        mod panicking {
            #[requires(false)]
            fn panic(expr: &'static str) -> !;

            #[requires(false)]
            fn assert_failed<T, U>(kind: AssertKind, left: &T, right: &U, args: Option<fmt::Arguments<'_>>) -> !
            where
                T: fmt::Debug + ?Sized,
                U: fmt::Debug + ?Sized;
        }
    }

    mod std {
        mod rt {
            #[requires(false)]
            fn begin_panic<M: Any + Send>(msg: M) -> !;
        }
    }
}
