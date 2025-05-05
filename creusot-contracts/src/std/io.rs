use crate::*;
use ::std::fmt;

extern_spec! {
    mod std {
        mod io {
            // This is an implementation detail of `std`: we specify it so that we can use
            // `print!` and `println!`.
            #[ensures(true)]
            fn _print(args: fmt::Arguments<'_>) {}

            // This is an implementation detail of `std`: we specify it so that we can use
            // `eprint!` and `eprintln!`.
            #[ensures(true)]
            fn _eprint(args: fmt::Arguments<'_>) {}
        }
    }
}
