//! A preprocessing phase for the `ghost!` macro.
//!
//! This should be kept to a minimum in order to minimize the mismatch between ghost and
//! normal code.

use proc_macro::{Delimiter, Group, Ident, Literal, Punct, TokenStream, TokenTree};

// FIXME: deduplicate this and the creusot_contracts_dummy version.
/// Change `xxxint` into `*::creusot_contracts::Int::new(xxx)`.
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
                    let span = literal.span();
                    let mut star = Punct::new('*', proc_macro::Spacing::Alone);
                    star.set_span(span);
                    let mut colon1 = Punct::new(':', proc_macro::Spacing::Joint);
                    colon1.set_span(span);
                    let mut colon2 = Punct::new(':', proc_macro::Spacing::Alone);
                    colon2.set_span(span);
                    let creusot_contract = Ident::new("creusot_contracts", span);
                    let int = Ident::new("Int", span);
                    let new = Ident::new("new", span);
                    let mut group = Group::new(
                        Delimiter::None,
                        vec![
                            TokenTree::Punct(star),
                            TokenTree::Punct(colon1.clone()),
                            TokenTree::Punct(colon2.clone()),
                            TokenTree::Ident(creusot_contract),
                            TokenTree::Punct(colon1.clone()),
                            TokenTree::Punct(colon2.clone()),
                            TokenTree::Ident(int),
                            TokenTree::Punct(colon1),
                            TokenTree::Punct(colon2),
                            TokenTree::Ident(new),
                            TokenTree::Group({
                                let mut lit = Literal::i128_suffixed(lit.parse::<i128>().unwrap());
                                lit.set_span(span);
                                let mut args = Group::new(
                                    Delimiter::Parenthesis,
                                    TokenTree::Literal(lit).into(),
                                );
                                args.set_span(span);
                                args
                            }),
                        ]
                        .into_iter()
                        .collect(),
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
