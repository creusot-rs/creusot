use crate::*;
#[cfg(creusot)]
use ::std::fmt::{Arguments, Debug, Formatter};

extern_spec! {
    mod core {
        mod fmt {
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

extern_spec! {
    mod core {
        mod fmt {
            impl<'a> Arguments<'a> {
                #[requires(true)]
                fn new_const<const N: usize>(pieces: &'a [&'static str; N]) -> Self;
            }
        }
    }
}
