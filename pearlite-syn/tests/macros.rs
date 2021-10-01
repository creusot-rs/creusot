pub mod debug;

#[macro_export]
macro_rules! snapshot {
    ($($args:tt)*) => {
        snapshot_impl!(() $($args)*)
    };
}

#[macro_export]
macro_rules! snapshot_impl {
    (($expr:ident) as $t:ty, @$snapshot:literal) => {
        let $expr = crate::macros::Tokens::parse::<$t>($expr).unwrap();
        // let debug = crate::macros::debug::Lite(&$expr);
        let debug = $expr;
        insta::assert_debug_snapshot!(debug, @$snapshot);
    };
    (($($expr:tt)*) as $t:ty, @$snapshot:literal) => {{
        let syntax_tree = crate::macros::Tokens::parse::<$t>($($expr)*).unwrap();
        // let debug = crate::macros::debug::Lite(&syntax_tree);
        // let debug = syntax_tree;
        insta::assert_debug_snapshot!(&syntax_tree, @$snapshot);
        syntax_tree
    }};
    (($($expr:tt)*) , @$snapshot:literal) => {{
        let syntax_tree = $($expr)*;
        let debug = crate::macros::debug::Lite(&syntax_tree);
        insta::assert_debug_snapshot!(debug, @$snapshot);
        syntax_tree
    }};
    (($($expr:tt)*) $next:tt $($rest:tt)*) => {
        snapshot_impl!(($($expr)* $next) $($rest)*)
    };
}

use syn::{parse::Parse, Result};

pub trait Tokens {
    fn parse<T: Parse>(self) -> Result<T>;
}

impl<'a> Tokens for &'a str {
    fn parse<T: Parse>(self) -> Result<T> {
        syn::parse_str(self)
    }
}

impl Tokens for proc_macro2::TokenStream {
    fn parse<T: Parse>(self) -> Result<T> {
        syn::parse2(self)
    }
}
