use crate::prelude::*;
#[cfg(creusot)]
use core::fmt::Arguments;

extern_spec! {
    mod std {
        mod io {
            /// This is an implementation detail of `std`: we specify it so that we can use
            /// `print!` and `println!`.
            #[check(terminates)]
            #[ensures(true)]
            fn _print(args: Arguments<'_>) {}

            /// This is an implementation detail of `std`: we specify it so that we can use
            /// `eprint!` and `eprintln!`.
            #[check(terminates)]
            #[ensures(true)]
            fn _eprint(args: Arguments<'_>) {}
        }
    }
}
