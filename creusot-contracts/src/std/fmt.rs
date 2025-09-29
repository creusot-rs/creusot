use crate::*;
#[cfg(creusot)]
use ::std::fmt::{Arguments, Debug, Error, Formatter};

extern_spec! {
    mod core {
        mod fmt {
            impl<'a> Formatter<'a> {
                #[requires(true)]
                fn write_str(&mut self, data: &str) -> Result<(), Error>;

                #[requires(true)]
                fn debug_struct_field1_finish<'b>(
                    &'b mut self,
                    name: &str,
                    name1: &str,
                    value1: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_struct_field2_finish<'b>(
                    &'b mut self,
                    name: &str,
                    name1: &str,
                    value1: &dyn Debug,
                    name2: &str,
                    value2: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_struct_field3_finish<'b>(
                    &'b mut self,
                    name: &str,
                    name1: &str,
                    value1: &dyn Debug,
                    name2: &str,
                    value2: &dyn Debug,
                    name3: &str,
                    value3: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_struct_field4_finish<'b>(
                    &'b mut self,
                    name: &str,
                    name1: &str,
                    value1: &dyn Debug,
                    name2: &str,
                    value2: &dyn Debug,
                    name3: &str,
                    value3: &dyn Debug,
                    name4: &str,
                    value4: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_struct_field5_finish<'b>(
                    &'b mut self,
                    name: &str,
                    name1: &str,
                    value1: &dyn Debug,
                    name2: &str,
                    value2: &dyn Debug,
                    name3: &str,
                    value3: &dyn Debug,
                    name4: &str,
                    value4: &dyn Debug,
                    name5: &str,
                    value5: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_struct_fields_finish<'b>(
                    &'b mut self,
                    name: &str,
                    names: &[&str],
                    values: &[&dyn Debug],
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_tuple_field1_finish<'b>(
                    &'b mut self,
                    name: &str,
                    value1: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_tuple_field2_finish<'b>(
                    &'b mut self,
                    name: &str,
                    value1: &dyn Debug,
                    value2: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_tuple_field3_finish<'b>(
                    &'b mut self,
                    name: &str,
                    value1: &dyn Debug,
                    value2: &dyn Debug,
                    value3: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_tuple_field4_finish<'b>(
                    &'b mut self,
                    name: &str,
                    value1: &dyn Debug,
                    value2: &dyn Debug,
                    value3: &dyn Debug,
                    value4: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_tuple_field5_finish<'b>(
                    &'b mut self,
                    name: &str,
                    value1: &dyn Debug,
                    value2: &dyn Debug,
                    value3: &dyn Debug,
                    value4: &dyn Debug,
                    value5: &dyn Debug,
                ) -> ::std::fmt::Result;

                #[requires(true)]
                fn debug_tuple_fields_finish<'b>(
                    &'b mut self,
                    name: &str,
                    values: &[&dyn Debug],
                ) -> ::std::fmt::Result;
            }
        }
    }
}

extern_spec! {
    mod core {
        mod fmt {
            impl<'a> Arguments<'a> {
                #[check(ghost)]
                #[requires(N <= 1usize)]
                fn new_const<const N: usize>(pieces: &'a [&'static str; N]) -> Self;
            }
        }
    }
}
