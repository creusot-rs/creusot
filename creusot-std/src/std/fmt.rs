use crate::prelude::*;
#[cfg(creusot)]
use core::fmt::{Debug, Formatter, Result};

extern_spec! {
    impl<'a> Formatter<'a> {
        fn write_str(&mut self, data: &str) -> Result;

        fn debug_struct_field1_finish<'b>(
            &'b mut self,
            names: &str,
            value1: &dyn Debug,
        ) -> Result;

        fn debug_struct_field2_finish<'b>(
            &'b mut self,
            names: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
        ) -> Result;

        fn debug_struct_field3_finish<'b>(
            &'b mut self,
            names: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
            value3: &dyn Debug,
        ) -> Result;

        fn debug_struct_field4_finish<'b>(
            &'b mut self,
            names: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
            value3: &dyn Debug,
            value4: &dyn Debug,
        ) -> Result;

        fn debug_struct_field5_finish<'b>(
            &'b mut self,
            names: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
            value3: &dyn Debug,
            value4: &dyn Debug,
            value5: &dyn Debug,
        ) -> Result;

        fn debug_struct_fields_finish<'b>(
            &'b mut self,
            names: &str,
            values: &[&dyn Debug],
        ) -> Result;
    }

    impl<'a> core::fmt::Arguments<'a> {
        #[check(ghost)]
        fn from_str(s: &'static str) -> Self;
    }
}
