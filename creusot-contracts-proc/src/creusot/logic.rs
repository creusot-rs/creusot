//! Macros for defining logical functions

use crate::{
    common::FilterAttrs as _,
    creusot::{
        doc::{self, document_spec},
        generate_unique_ident, pretyping,
    },
};
use pearlite_syn::TBlock;
use proc_macro::TokenStream as TS1;
use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, TokenStreamExt as _, quote, quote_spanned};
use syn::{
    Attribute, Error, Ident, Item, Result, Signature, Token, VisRestricted, Visibility, braced,
    parenthesized,
    parse::{Parse, ParseStream},
    parse_macro_input,
    punctuated::Punctuated,
    spanned::Spanned as _,
};

#[derive(Debug)]
struct LogicItem {
    attrs: Vec<Attribute>,
    vis: Visibility,
    sig: Signature,
    body: Box<TBlock>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TraitItemSignature {
    attrs: Vec<Attribute>,
    sig: Signature,
    semi_token: Token![;],
}

#[derive(Debug)]
enum LogicInput {
    Item(LogicItem),
    Sig(TraitItemSignature),
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct LogicTags {
    open: Option<Visibility>,
    opaque: bool,
    law: bool,
    prophetic: bool,
    sealed: bool,
    inline: bool,
}

#[derive(Clone, Debug)]
enum LogicTag {
    Open(Visibility, Span),
    Opaque(Span),
    Law(Span),
    Prophetic(Span),
    Sealed(Span),
    Inline(Span),
}

pub fn logic(in_tags: TS1, tokens: TS1) -> TS1 {
    let mut tags = LogicTags::default();
    for tag in parse_macro_input!(in_tags with Punctuated<LogicTag, Token![,]>::parse_terminated) {
        if let Err(e) = tags.add(tag) {
            return e.into_compile_error().into();
        }
    }
    if tags.opaque && tags.open.is_some() {
        return Error::new(
            Span::call_site(),
            "`open` and `opaque` cannot be specified at the same time",
        )
        .into_compile_error()
        .into();
    }

    let log = parse_macro_input!(tokens as LogicInput);

    let documentation = document_spec(
        &tags.doc_str(),
        if let Some(Visibility::Public(_)) = tags.open {
            log.logic_body()
        } else {
            doc::LogicBody::Opaque
        },
    );

    match log {
        LogicInput::Item(LogicItem { attrs, vis, sig, mut body }) => {
            let span = sig.span();
            let (tags_toks, open_toks) = tags.tokens(&sig.ident);

            if let Some(open_toks) = open_toks {
                body.stmts.insert(0, pearlite_syn::TermStmt::Item(Item::Verbatim(open_toks)));
            }
            let req_body = pretyping::encode_block(&body);

            TS1::from(quote_spanned! {span =>
                #tags_toks
                #(#attrs)*
                #documentation
                #vis #sig #req_body
            })
        }
        LogicInput::Sig(TraitItemSignature { attrs, sig, semi_token }) => {
            let span = sig.span();

            if tags.open.is_some() || tags.opaque {
                return Error::new(
                    Span::call_site(),
                    "Cannot mark trait item signature as open or opaque",
                )
                .into_compile_error()
                .into();
            }

            let (tags_toks, open_toks) = tags.tokens(&sig.ident);
            assert!(open_toks.is_none());

            TS1::from(quote_spanned! {span =>
                #tags_toks
                #(#attrs)*
                #documentation
                #sig #semi_token
            })
        }
    }
}

pub fn pearlite(tokens: TS1) -> TS1 {
    let block = parse_macro_input!(tokens with TBlock::parse_within);
    TS1::from(
        block
            .iter()
            .map(pretyping::encode_stmt)
            .collect::<std::result::Result<TokenStream, _>>()
            .unwrap_or_else(|e| e.into_tokens()),
    )
}

impl ToTokens for TraitItemSignature {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.append_all(self.attrs.outer());
        self.sig.to_tokens(tokens);
        self.semi_token.to_tokens(tokens);
    }
}

impl Parse for LogicInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let attrs = input.call(Attribute::parse_outer)?;
        let vis: Visibility = input.parse()?;
        let defaultness: Option<Token![default]> = input.parse()?;
        if defaultness.is_some() {
            return Err(Error::new(
                input.span(),
                "logical functions cannot use the `default` modifier",
            ));
        }
        let sig: Signature = input.parse()?;
        if input.peek(Token![;]) {
            let semi_token: Token![;] = input.parse()?;
            Ok(LogicInput::Sig(TraitItemSignature { attrs, sig, semi_token }))
        } else {
            let body;
            let brace_token = braced!(body in input);
            let body = Box::new(TBlock { brace_token, stmts: body.call(TBlock::parse_within)? });
            Ok(LogicInput::Item(LogicItem { attrs, vis, sig, body }))
        }
    }
}

impl LogicInput {
    fn logic_body(&self) -> doc::LogicBody {
        match self {
            LogicInput::Item(log_item) => {
                if doc::is_opaque(&log_item.attrs) {
                    doc::LogicBody::Opaque
                } else {
                    doc::LogicBody::Some(log_item.body.to_token_stream().into())
                }
            }
            LogicInput::Sig(_) => doc::LogicBody::None,
        }
    }
}

impl Parse for LogicTag {
    fn parse(input: ParseStream) -> Result<Self> {
        let ident: Ident = input.parse()?;
        match ident.to_string().as_str() {
            "open" => {
                if input.is_empty() || input.peek(Token![,]) {
                    return Ok(Self::Open(Visibility::Public(Default::default()), ident.span()));
                }
                let vis;
                let paren_token = parenthesized!(vis in input);
                let span = ident.span().join(paren_token.span.span()).unwrap();
                Ok(Self::Open(
                    Visibility::Restricted(VisRestricted {
                        pub_token: Default::default(),
                        paren_token,
                        in_token: vis.parse()?,
                        path: vis.parse()?,
                    }),
                    span,
                ))
            }
            "opaque" => Ok(Self::Opaque(ident.span())),
            "law" => Ok(Self::Law(ident.span())),
            "prophetic" => Ok(Self::Prophetic(ident.span())),
            "sealed" => Ok(Self::Sealed(ident.span())),
            "inline" => Ok(Self::Inline(ident.span())),
            _ => Err(Error::new(
                ident.span(),
                "unsupported modifier. The only supported modifiers are `open`, `prophetic`, `law` and `sealed`",
            )),
        }
    }
}

macro_rules! impl_logic_tag {
    ($($variant:ident => ($($attr:tt)+))*) => {
        impl LogicTags {
            $(
                fn $variant(&mut self, span: Span) -> Result<()> {
                    if std::mem::replace(&mut self.$variant, true) {
                        return Err(Error::new(span, concat!("`", stringify!($variant), "` can only be specified once.")));
                    }
                    Ok(())
                }
            )*

            fn open(&mut self, span: Span, vis: Visibility) -> Result<()> {
                if std::mem::replace(&mut self.open, Some(vis)).is_some() {
                    return Err(Error::new(span, "`open` can only be specified once."));
                }
                Ok(())
            }

            fn doc_str(&self) -> String {
                let mut doc_str = String::new();
                let mut push = |s: &str| {
                    if doc_str.is_empty() {
                        doc_str.push('(');
                    } else {
                        doc_str.push_str(", ");
                    }
                    doc_str.push_str(s);
                };

                if let Some(vis) = &self.open {
                    let mut str = String::from("open");
                    if let Visibility::Restricted(vis) = vis {
                        str.push_str(&format!("({})", vis.to_token_stream()));
                    }
                    push(&str);
                }

                $(
                    if self.$variant {
                        push(stringify!($variant));
                    }
                )*

                if !doc_str.is_empty() {
                    doc_str.push(')')
                }

                doc_str
            }

            fn tokens(&self, nm: &Ident) -> (TokenStream, Option<TokenStream>) {
                let (mut tokens, mut inner_toks) = (TokenStream::new(), None);
                tokens.extend(quote!(#[creusot::decl::logic]));
                if let Some(vis) = &self.open {
                    let open_name = generate_unique_ident(&nm.to_string(), Span::call_site());
                    let name_tag = open_name.to_string();
                    inner_toks = Some(quote! {
                        #[creusot::no_translate]
                        #[creusot::item=#name_tag]
                        #vis fn #open_name() {}
                    });

                    tokens.extend(quote!(#[creusot::clause::open=#name_tag]));
                }
                $(
                    if self.$variant {
                        tokens.extend(quote!($($attr)+));
                    }
                )*
                (tokens, inner_toks)
            }
        }
    };
}

impl_logic_tag!(
    opaque =>    (#[creusot::decl::opaque])
    law =>       (#[creusot::decl::logic::law])
    prophetic => (#[creusot::decl::logic::prophetic])
    sealed =>    (#[creusot::decl::logic::sealed])
    inline =>    (#[creusot::decl::logic::inline])
);

impl LogicTags {
    fn add(&mut self, tag: LogicTag) -> Result<()> {
        match tag {
            LogicTag::Open(vis, span) => self.open(span, vis)?,
            LogicTag::Opaque(span) => self.opaque(span)?,
            LogicTag::Law(span) => self.law(span)?,
            LogicTag::Prophetic(span) => self.prophetic(span)?,
            LogicTag::Sealed(span) => self.sealed(span)?,
            LogicTag::Inline(span) => self.inline(span)?,
        }
        Ok(())
    }
}
