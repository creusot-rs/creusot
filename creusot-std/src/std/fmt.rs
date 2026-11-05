use crate::prelude::*;
#[cfg(creusot)]
use core::fmt::{Alignment, Arguments, Debug, FormattingOptions, Result, Sign};
use core::fmt::{Formatter, Write};

pub trait FormatterExt {
    /// Whether the underlying stream may fail.
    ///
    /// In particular, this is `false` when writing to a `String`.
    #[logic]
    fn faillible(self) -> bool;

    /// Postcondition for `Formatter` methods
    #[logic(sealed, open, prophetic)]
    fn fmt_result(&mut self, r: Result) -> bool {
        pearlite! {
            (^self).faillible() == (*self).faillible() &&
            match r {
                Ok(_) => true,
                Err(_) => (*self).faillible()
            }
        }
    }
}

impl FormatterExt for Formatter<'_> {
    #[logic(opaque)]
    fn faillible(self) -> bool {
        dead
    }
}

#[trusted]
#[ensures(forall<write: &mut _, options: FormattingOptions, fmt: Formatter>
    *write == *result && Formatter::new.postcondition((write, options,), fmt) ==> !fmt.faillible()
)]
pub fn string_to_write(s: &mut String) -> &mut dyn Write {
    &mut *s
}

extern_spec! {
    impl<'a> Formatter<'a> {
        /// Note: Creusot doesn't support casting to `dyn`.
        /// For the special case of writing to a `String` infaillibly,
        /// use [`string_to_write`] to cast from `String` to `dyn Write`.
        fn new(write: &'a mut (dyn Write + 'a), options: FormattingOptions) -> Self;

        #[ensures(result.faillible() == self.faillible() && (^self).faillible() == (*self).faillible())]
        fn with_options<'b>(&'b mut self, options: FormattingOptions) -> Formatter<'b>;

        #[ensures(self.fmt_result(result))]
        fn pad_integral(&mut self, is_nonnegative: bool, prefix: &str, buf: &str) -> Result;

        #[ensures(self.fmt_result(result))]
        fn pad(&mut self, s: &str) -> Result;

        #[ensures(self.fmt_result(result))]
        fn write_str(&mut self, data: &str) -> Result;

        #[ensures(self.fmt_result(result))]
        fn write_fmt(&mut self, args: Arguments<'_>) -> Result;

        fn fill(&self) -> char;
        fn align(&self) -> Option<Alignment>;
        fn width(&self) -> Option<usize>;
        fn precision(&self) -> Option<usize>;
        fn sign_plus(&self) -> bool;
        fn sign_minus(&self) -> bool;
        fn alternate(&self) -> bool;
        fn sign_aware_zero_pad(&self) -> bool;
        fn sign(&self) -> Option<Sign>;
        fn options(&self) -> FormattingOptions;

        #[ensures(self.fmt_result(result))]
        fn debug_struct_field1_finish<'b>(
            &'b mut self,
            name: &str,
            name1: &str,
            value1: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_struct_field2_finish<'b>(
            &'b mut self,
            name: &str,
            name1: &str,
            value1: &dyn Debug,
            name2: &str,
            value2: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_struct_field3_finish<'b>(
            &'b mut self,
            name: &str,
            name1: &str,
            value1: &dyn Debug,
            name2: &str,
            value2: &dyn Debug,
            name3: &str,
            value3: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
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
        ) -> Result;

        #[ensures(self.fmt_result(result))]
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
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_struct_fields_finish<'b>(
            &'b mut self,
            name: &str,
            names: &[&str],
            values: &[&dyn Debug],
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_tuple_field1_finish<'b>(
            &'b mut self,
            name: &str,
            value1: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_tuple_field2_finish<'b>(
            &'b mut self,
            name: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_tuple_field3_finish<'b>(
            &'b mut self,
            name: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
            value3: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_tuple_field4_finish<'b>(
            &'b mut self,
            name: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
            value3: &dyn Debug,
            value4: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_tuple_field5_finish<'b>(
            &'b mut self,
            name: &str,
            value1: &dyn Debug,
            value2: &dyn Debug,
            value3: &dyn Debug,
            value4: &dyn Debug,
            value5: &dyn Debug,
        ) -> Result;

        #[ensures(self.fmt_result(result))]
        fn debug_tuple_fields_finish<'b>(
            &'b mut self,
            name: &str,
            values: &[&dyn Debug],
        ) -> Result;
    }

    impl Write for Formatter<'_> {
        #[ensures(self.fmt_result(result))]
        fn write_str(&mut self, s: &str) -> Result;

        #[ensures(self.fmt_result(result))]
        fn write_char(&mut self, c: char) -> Result;

        #[ensures(self.fmt_result(result))]
        fn write_fmt(&mut self, args: Arguments<'_>) -> Result;
    }

    impl<'a> core::fmt::Arguments<'a> {
        #[check(ghost)]
        fn from_str(s: &'static str) -> Self;
    }
}
