//! A preprocessing phase for the `ghost!` macro.
//!
//! This should be kept to a minimum in order to minimize the mismatch between ghost and
//! normal code.

use proc_macro2::{Delimiter, Group, Literal, TokenStream, TokenTree};
use quote::quote_spanned;

/// Change `xxxint` into `*::creusot_std::logic::Int::new(xxx)`.
pub(crate) fn ghost_preprocess(tokens: TokenStream) -> TokenStream {
    tokens
        .into_iter()
        .map(|t| match t {
            TokenTree::Group(group) => {
                let mut result = Group::new(group.delimiter(), ghost_preprocess(group.stream()));
                result.set_span(group.span());
                TokenTree::Group(result)
            }
            TokenTree::Literal(literal) => {
                let lit = literal.to_string();
                if let Some(lit) = lit.strip_suffix("int") {
                    let span = proc_macro2::Span::from(literal.span());
                    let mut lit = Literal::i128_suffixed(lit.parse::<i128>().unwrap());
                    lit.set_span(span);
                    let mut group = Group::new(
                        Delimiter::None,
                        quote_spanned!(span => ::creusot_std::ghost::Ghost::into_inner(::creusot_std::logic::Int::new(#lit))).into(),
                    );
                    group.set_span(literal.span());
                    TokenTree::Group(group)
                } else {
                    TokenTree::Literal(literal)
                }
            }
            TokenTree::Ident(_) | TokenTree::Punct(_) => t,
        })
        .collect()
}
