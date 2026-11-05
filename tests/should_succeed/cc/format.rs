#![feature(formatting_options)]
extern crate creusot_std;
use creusot_std::{prelude::*, std::fmt::*};
use std::fmt::{Formatter, Write as _};

pub fn f() {
    let mut s = String::new();
    let mut fmt = Formatter::new(string_to_write(&mut s), Default::default());
    fmt.write_str("a").unwrap();
    fmt.write_char('b').unwrap();
}
