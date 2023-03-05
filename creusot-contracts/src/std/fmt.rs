use crate::*;
#[cfg(feature = "contracts")]
use ::std::fmt::{ArgumentV1, Arguments, Debug, Formatter};

extern_spec! {
    mod std {
        mod io {
            #[requires(true)]
            fn _print(fmt: std::fmt::Arguments<'_>);
        }

        mod fmt {
            impl<'a> ArgumentV1<'a> {
            #[requires(true)]
            fn new_debug<'b, T : Debug>(x: &'b T) -> ArgumentV1<'_>;
            }

            impl<'a> Arguments<'a> {
                #[requires(true)]
                fn new_v1(pieces: &'a [&'static str], args: &'a [std::fmt::ArgumentV1<'a>]) -> std::fmt::Arguments<'a>;
            }

            impl<'a> Formatter<'a> {
                #[requires(true)]
                fn debug_struct_field1_finish<'b>(
                    &'b mut self,
                    name: &str,
                    name1: &str,
                    value1: &dyn Debug,
                ) -> ::std::fmt::Result;
            }
        }
    }
}
